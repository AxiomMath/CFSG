module

public import CFSG.CGT.PushingUpLit.SolKNA.Prop18
public import CFSG.RankThree.GF2n.ConjModule
public import CFSG.RankThree.GF2n.NaturalDecomp
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.RankThree.GF2n.BenderStrongWC

public section

open scoped IsMulCommutative

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.Timmesfeld.RankOne Matrix
open CFSG.RankThree.GF2n
  (conjHom conjEndHom coe_conjHom_apply conjEndHom_apply supIndep_image_of_lattice_hom
    sup_image_of_sup_hom exists_supIndep_natural)
open scoped MatrixGroups

theorem utri_eq_upperUnipotent' (F : Type) [Field F] : utri F = upperUnipotent F := by
  ext g
  rw [mem_utri_iff, mem_upperUnipotent_iff F]
  have e : ∀ s : F, utriElt s = upperElt F s := fun s =>
    sl2_ext (by simp [utriElt_apply_00, upperElt]) (by simp [utriElt_apply_01, upperElt])
      (by simp [utriElt_apply_10, upperElt]) (by simp [utriElt_apply_11, upperElt])
  simp only [e]

variable {X : Type} [Group X] [Finite X]

namespace Prop18Setup

variable {R Rb L Lb N : Subgroup X} (S : Prop18Setup R Rb L Lb N)
include S

theorem isMulCommutative_N : IsMulCommutative ↥N :=
  ⟨⟨fun a b => Subtype.ext (S.comm_N a.2 b.2)⟩⟩

theorem comm_mem_L {y m : X} (hy : y ∈ R) (hm : m ∈ N) : y * m * y⁻¹ * m⁻¹ ∈ L := by
  have h1 := S.comm_R_N hy hm
  have h2 : y * m * y⁻¹ * m⁻¹ ∈ N :=
    N.mul_mem (by simpa [mul_assoc] using S.normal.conj_mem m hm y) (N.inv_mem hm)
  rw [← S.inf_N]
  exact Subgroup.mem_inf.mpr ⟨h1, h2⟩

theorem eq_one_of_commute {a b m : X} (ha : a ∈ R) (haN : a ∉ N) (hb : b ∈ Rb) (hbN : b ∉ N)
    (hm : m ∈ N) (hma : a * m = m * a) (hmb : b * m = m * b) : m = 1 := by
  have h1 := S.cent_R ha haN hm hma
  have h2 := S.symm.cent_R hb hbN hm hmb
  have h3 : m ∈ R ⊓ Rb := Subgroup.mem_inf.mpr ⟨h1, h2⟩
  rwa [S.inf_eq_bot, Subgroup.mem_bot] at h3

theorem commutator_injective {a : X} (ha : a ∈ R) (haN : a ∉ N) :
    Function.Injective fun n : ↥Lb =>
      (⟨a * n * a⁻¹ * (n : X)⁻¹, S.comm_mem_L ha (S.Lb_le_N n.2)⟩ : ↥L) := by
  intro n₁ n₂ h
  have h' : a * (n₁ : X) * a⁻¹ * (n₁ : X)⁻¹ = a * n₂ * a⁻¹ * (n₂ : X)⁻¹ := congrArg Subtype.val h
  have h2 : (n₁ : X) * a⁻¹ * (n₁ : X)⁻¹ = n₂ * a⁻¹ * (n₂ : X)⁻¹ := by
    calc (n₁ : X) * a⁻¹ * (n₁ : X)⁻¹ = a⁻¹ * (a * n₁ * a⁻¹ * (n₁ : X)⁻¹) := by group
      _ = a⁻¹ * (a * n₂ * a⁻¹ * (n₂ : X)⁻¹) := by rw [h']
      _ = n₂ * a⁻¹ * (n₂ : X)⁻¹ := by group
  have hc : a * ((n₂ : X)⁻¹ * n₁) = ((n₂ : X)⁻¹ * n₁) * a := by
    calc a * ((n₂ : X)⁻¹ * n₁) = a * ((n₂ : X)⁻¹ * (n₁ * a⁻¹ * (n₁ : X)⁻¹) * n₁ * a) := by group
      _ = a * ((n₂ : X)⁻¹ * (n₂ * a⁻¹ * (n₂ : X)⁻¹) * n₁ * a) := by rw [h2]
      _ = ((n₂ : X)⁻¹ * n₁) * a := by group
  have hmN : (n₂ : X)⁻¹ * n₁ ∈ N := N.mul_mem (N.inv_mem (S.Lb_le_N n₂.2)) (S.Lb_le_N n₁.2)
  have hmLb : (n₂ : X)⁻¹ * n₁ ∈ Lb := Lb.mul_mem (Lb.inv_mem n₂.2) n₁.2
  have h1 : (n₂ : X)⁻¹ * n₁ ∈ R ⊓ Rb :=
    Subgroup.mem_inf.mpr ⟨S.cent_R ha haN hmN hc, S.Lb_le hmLb⟩
  rw [S.inf_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at h1
  exact Subtype.ext h1.symm

theorem exists_commutator_eq {a l : X} (ha : a ∈ R) (haN : a ∉ N) (hl : l ∈ L) :
    ∃ n ∈ Lb, a * n * a⁻¹ * n⁻¹ = l := by
  obtain ⟨n, hn⟩ :=
    ((S.commutator_injective ha haN).bijective_of_nat_card_le S.card_eq.ge).2 ⟨l, hl⟩
  exact ⟨n, n.2, congrArg Subtype.val hn⟩

section Psl

variable [N.Normal]

theorem exists_sl2_equiv {f : ℕ} (hf : 2 ≤ f) (e : X ⧸ N ≃* PSL(2, GaloisField 2 f)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (e' : X ⧸ N ≃* SL(2, F)),
      Nat.card F = 2 ^ f ∧
        (R.map (QuotientGroup.mk' N)).map e'.toMonoidHom = upperUnipotent F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := S.ncPair.strongWC
  have hT0 := S.ncPair.ne_bot
  obtain ⟨P, hTP⟩ := (CFSG.RankThree.GF2n.isPGroup_of_strongWC hS).exists_le_sylow
  have hL2 := IsL2Pair.of_psl_sylow (by omega : f ≠ 0) ⟨e⟩ P
  have hTeq := hL2.eq_of_isWC hTP hT0 hS.isWC
  rw [← hTeq] at hL2
  obtain ⟨F, hF, hFin, hchar, e', hcard, hmap⟩ := hL2
  exact ⟨F, hF, hFin, hchar, e', hcard, by rw [hmap, utri_eq_upperUnipotent']⟩

theorem struct_psl {f : ℕ} (hf : 2 ≤ f) (e : X ⧸ N ≃* PSL(2, GaloisField 2 f)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (ψ : X →* SL(2, F)),
      Nat.card F = 2 ^ f ∧ Function.Surjective ψ ∧ ψ.ker = N ∧ R.map ψ = upperUnipotent F ∧
      ∃ s : Finset (Subgroup X), s.SupIndep id ∧ s.sup id = N ∧
        ∀ W ∈ s, W ≤ N ∧ W.Normal ∧ W ≠ ⊥ ∧
          (∀ U : Subgroup X, U ≤ W → U.Normal → U = ⊥ ∨ U = W) ∧
          ∃ θ : (Fin 2 → F) → X, (∀ v v', θ (v + v') = θ v * θ v') ∧ Function.Injective θ ∧
            Set.range θ = W ∧ ∀ (x : X) (v : Fin 2 → F),
              θ ((ψ x : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = x * θ v * x⁻¹ := by
  classical
  have hcomm := S.isMulCommutative_N
  let : Module (ZMod 2) (Additive ↥N) := AddCommGroup.zmodModule fun v => by
    rw [two_nsmul]
    exact Additive.toMul.injective (Subtype.ext (S.sq_N _ v.toMul.2))
  obtain ⟨F, hF, hFin, hchar, e', hcard, hmap⟩ := S.exists_sl2_equiv hf e
  set ψ : X →* SL(2, F) := e'.toMonoidHom.comp (QuotientGroup.mk' N) with hψ
  have hψs : Function.Surjective ψ := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψk : ψ.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, mk_eq_one_iff]
  have hψR : R.map ψ = upperUnipotent F := by
    rw [hψ, ← Subgroup.map_map]
    exact hmap
  have hXN : ∀ x : X, x ∈ Subgroup.normalizer (N : Set X) := fun x => by
    rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : N.Normal)]
    exact Subgroup.mem_top x
  set φ₀ : X →* Module.End (ZMod 2) (Additive ↥N) :=
    (conjEndHom N).comp (MonoidHom.codRestrict (MonoidHom.id X) _ hXN) with hφ₀
  have hφ₀x : ∀ (x : X) (v : Additive ↥N),
      ((φ₀ x v).toMul : X) = x * (v.toMul : X) * x⁻¹ := fun _ _ => rfl
  have hker : N ≤ φ₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    refine LinearMap.ext fun v => Additive.toMul.injective (Subtype.ext ?_)
    rw [hφ₀x, S.comm_N hx v.toMul.2, mul_inv_cancel_right]
    rfl
  set ρ : SL(2, F) →* Module.End (ZMod 2) (Additive ↥N) :=
    (QuotientGroup.lift N φ₀ hker).comp e'.symm.toMonoidHom with hρ
  let : DistribMulAction SL(2, F) (Additive ↥N) := DistribMulAction.compHom _ ρ
  have hsmul : ∀ (x : X) (v : Additive ↥N), ψ x • v = φ₀ x v := by
    intro x v
    show ρ (ψ x) v = φ₀ x v
    rw [hρ, hψ, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, QuotientGroup.mk'_apply,
      QuotientGroup.lift_mk]
  have hsub : ∀ v w : Additive ↥N,
      (((v - w).toMul : ↥N) : X) = ((v.toMul : ↥N) : X) * ((w.toMul : ↥N) : X)⁻¹ := fun v w => by
    rw [toMul_sub, Subgroup.coe_div, div_eq_mul_inv]
  have hupper : ∀ g ∈ upperUnipotent F, ∃ y : X, y ∈ R ∧ ψ y = g := by
    intro g hg
    rw [← hψR] at hg
    obtain ⟨y, hy, rfl⟩ := hg
    exact ⟨y, hy, rfl⟩
  obtain ⟨a, ha, haN⟩ := S.exists_mem_R_notMem_N
  obtain ⟨b, hb, hbN⟩ := S.symm.exists_mem_R_notMem_N
  have hfixφ : ∀ (x : X) (v : Additive ↥N), φ₀ x v = v →
      x * (v.toMul : X) = (v.toMul : X) * x := fun x v h => by
    have h' := congrArg (fun w : Additive ↥N => ((w.toMul : ↥N) : X)) h
    simp only [hφ₀x] at h'
    calc x * (v.toMul : X) = x * v.toMul * x⁻¹ * x := by group
      _ = (v.toMul : X) * x := by rw [h']
  have hfix : ∀ v : Additive ↥N, (∀ g : SL(2, F), g • v = v) → v = 0 := by
    intro v hv
    have h1 := hfixφ a v (by rw [← hsmul]; exact hv _)
    have h2 := hfixφ b v (by rw [← hsmul]; exact hv _)
    exact Additive.toMul.injective (Subtype.ext
      (S.eq_one_of_commute ha haN hb hbN v.toMul.2 h1 h2))
  have hcomA : ∀ (y : X), y ∈ R → ∀ v : Additive ↥N, ((v.toMul : ↥N) : X) ∈ L →
      φ₀ y v = v := fun y hy v hv => by
    refine Additive.toMul.injective (Subtype.ext ?_)
    rw [hφ₀x, (S.L_cent _ hv y hy).symm, mul_inv_cancel_right]
  have hquad : ∀ g ∈ upperUnipotent F, ∀ g' ∈ upperUnipotent F, ∀ v : Additive ↥N,
      g' • (g • v - v) = g • v - v := by
    intro g hg g' hg' v
    obtain ⟨y, hy, rfl⟩ := hupper g hg
    obtain ⟨y', hy', rfl⟩ := hupper g' hg'
    rw [hsmul, hsmul]
    apply hcomA y' hy'
    rw [hsub, hφ₀x]
    exact S.comm_mem_L hy v.toMul.2
  set Lsub : AddSubgroup (Additive ↥N) := Subgroup.toAddSubgroup (L.subgroupOf N) with hLsub
  have hLw : ∀ w ∈ Lsub, ∀ g ∈ upperUnipotent F, g • w = w := by
    intro w hw g hg
    obtain ⟨y, hy, rfl⟩ := hupper g hg
    rw [hsmul]
    exact hcomA y hy w (Subgroup.mem_subgroupOf.mp hw)
  have hgen : ∀ U : AddSubgroup (Additive ↥N), (∀ g : SL(2, F), ∀ v ∈ U, g • v ∈ U) →
      Lsub ≤ U → U = ⊤ := by
    intro U hU hLU
    have hUL : ∀ m : ↥N, (m : X) ∈ L → Additive.ofMul m ∈ U := fun m hm =>
      hLU (Subgroup.mem_subgroupOf.mpr hm)
    have hULb : ∀ m : ↥N, (m : X) ∈ Lb → Additive.ofMul m ∈ U := by
      intro m hm
      obtain ⟨n, hn, hnm⟩ := S.symm.exists_commutator_eq hb hbN hm
      have hnN : n ∈ N := S.L_le_N hn
      have h1 : Additive.ofMul (⟨n, hnN⟩ : ↥N) ∈ U := hUL ⟨n, hnN⟩ hn
      have h2 := hU (ψ b) _ h1
      rw [hsmul] at h2
      have h3 : φ₀ b (Additive.ofMul ⟨n, hnN⟩) - Additive.ofMul ⟨n, hnN⟩ =
          Additive.ofMul m := by
        refine Additive.toMul.injective (Subtype.ext ?_)
        rw [hsub, hφ₀x]
        exact hnm
      rw [← h3]
      exact U.sub_mem h2 h1
    rw [eq_top_iff]
    intro v _
    obtain ⟨l, hl, lb, hlb, he⟩ := S.exists_mul_of_mem_N v.toMul.2
    have hv : v = Additive.ofMul ⟨l, S.L_le_N hl⟩ + Additive.ofMul ⟨lb, S.Lb_le_N hlb⟩ :=
      Additive.toMul.injective (Subtype.ext he)
    rw [hv]
    exact U.add_mem (hUL _ hl) (hULb _ hlb)
  obtain ⟨s₀, hs₀, hs₀top, hs₀P⟩ := exists_supIndep_natural hfix hquad hLw hgen
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : AddSubgroup (Additive ↥N) → Subgroup X,
      ∀ W, Φ W = (Subgroup.toAddSubgroup.symm W).map N.subtype := ⟨_, fun _ => rfl⟩
  have hΦmem : ∀ (W : AddSubgroup (Additive ↥N)) (g : X),
      g ∈ Φ W ↔ ∃ h : g ∈ N, Additive.ofMul (⟨g, h⟩ : ↥N) ∈ W := by
    intro W g
    constructor
    · rw [hΦ]
      rintro ⟨m, hm, rfl⟩
      exact ⟨m.2, hm⟩
    · rintro ⟨h, hg⟩
      rw [hΦ]
      exact ⟨⟨g, h⟩, hg, rfl⟩
  have hΦnorm : ∀ W : AddSubgroup (Additive ↥N), (∀ g : SL(2, F), ∀ v ∈ W, g • v ∈ W) →
      (Φ W).Normal := by
    intro W hW
    refine ⟨fun n hn x => ?_⟩
    obtain ⟨hnN, hnW⟩ := (hΦmem W n).mp hn
    refine (hΦmem W _).mpr ⟨S.normal.conj_mem n hnN x, ?_⟩
    have := hW (ψ x) _ hnW
    rw [hsmul] at this
    exact this
  refine ⟨F, hF, hFin, hchar, ψ, hcard, hψs, hψk, hψR, s₀.image Φ,
    supIndep_image_of_lattice_hom hs₀ Φ ?_ ?_ ?_, ?_, ?_⟩
  · intro x y
    rw [hΦ, hΦ, hΦ, OrderIso.map_sup, Subgroup.map_sup]
  · intro x y
    rw [hΦ, hΦ, hΦ, OrderIso.map_inf, Subgroup.map_inf_eq _ _ _ N.subtype_injective]
  · rw [hΦ, OrderIso.map_bot, Subgroup.map_bot]
  · rw [sup_image_of_sup_hom s₀ Φ
      (fun x y => by rw [hΦ, hΦ, hΦ, OrderIso.map_sup, Subgroup.map_sup])
      (by rw [hΦ, OrderIso.map_bot, Subgroup.map_bot]), hs₀top, hΦ, OrderIso.map_top,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  intro W hW
  obtain ⟨W₀, hW₀, rfl⟩ := Finset.mem_image.mp hW
  obtain ⟨hW₀inv, hW₀0, hW₀irr, θ, hθinj, hθrange, hθ⟩ := hs₀P W₀ hW₀
  refine ⟨by rw [hΦ]; exact Subgroup.map_subtype_le _, hΦnorm W₀ hW₀inv, ?_, ?_, ?_⟩
  · intro h
    apply hW₀0
    have h' : Subgroup.toAddSubgroup.symm W₀ = ⊥ := by
      rwa [hΦ, ← Subgroup.map_bot N.subtype, (Subgroup.map_injective N.subtype_injective).eq_iff]
        at h
    rw [← OrderIso.apply_symm_apply Subgroup.toAddSubgroup W₀, h', OrderIso.map_bot]
  · intro U hUW hUN
    have hUM : U ≤ N := hUW.trans (by rw [hΦ]; exact Subgroup.map_subtype_le _)
    set U₀ : AddSubgroup (Additive ↥N) := Subgroup.toAddSubgroup (U.comap N.subtype) with hU₀
    have hU₀W : U₀ ≤ W₀ := by
      intro v hv
      have : ((v.toMul : ↥N) : X) ∈ Φ W₀ := hUW hv
      obtain ⟨h, hv'⟩ := (hΦmem W₀ _).mp this
      exact hv'
    have hU₀inv : ∀ g : SL(2, F), ∀ v ∈ U₀, g • v ∈ U₀ := by
      intro g v hv
      obtain ⟨x, hx⟩ := hψs g
      rw [← hx, hsmul]
      show ((φ₀ x v).toMul : X) ∈ U
      rw [hφ₀x]
      exact hUN.conj_mem _ hv x
    have hUe : Φ U₀ = U := by
      rw [hΦ, hU₀, OrderIso.symm_apply_apply, Subgroup.map_comap_eq, Subgroup.range_subtype,
        inf_of_le_right hUM]
    rcases hW₀irr U₀ hU₀W hU₀inv with h | h
    · left
      rw [← hUe, h, hΦ, OrderIso.map_bot, Subgroup.map_bot]
    · right
      rw [← hUe, h]
  · refine ⟨fun v => (((θ v).toMul : ↥N) : X), fun v v' => ?_, ?_, ?_, ?_⟩
    · show (((θ (v + v')).toMul : ↥N) : X) = (((θ v).toMul : ↥N) : X) * (((θ v').toMul : ↥N) : X)
      rw [map_add, toMul_add, Subgroup.coe_mul]
    · intro v v' h
      exact hθinj (Additive.toMul.injective (Subtype.ext h))
    · ext g
      rw [SetLike.mem_coe, hΦmem]
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨(θ v).toMul.2, by rw [← hθrange]; exact ⟨v, rfl⟩⟩
      · rintro ⟨h, hg⟩
        rw [← hθrange] at hg
        obtain ⟨v, hv⟩ := hg
        refine ⟨v, ?_⟩
        show (((θ v).toMul : ↥N) : X) = g
        rw [hv]
        rfl
    · intro x v
      show (((θ ((ψ x : Matrix (Fin 2) (Fin 2) F) *ᵥ v)).toMul : ↥N) : X) =
        x * (((θ v).toMul : ↥N) : X) * x⁻¹
      rw [hθ, hsmul]
      exact hφ₀x x (θ v)

end Psl

section Dihedral

omit S in
theorem inv_mul_mem_L_of_index_two {R L : Subgroup X} (hAL : L.relIndex R = 2) {a y : X}
    (ha : a ∈ R) (haL : a ∉ L) (hy : y ∈ R) (hyL : y ∉ L) : a⁻¹ * y ∈ L := by
  have h := (Subgroup.mul_mem_iff_of_index_two (H := L.subgroupOf R) hAL
    (a := (⟨a, ha⟩ : ↥R)⁻¹) (b := ⟨y, hy⟩)).mpr ⟨fun h => absurd (by
      have := (L.subgroupOf R).inv_mem h
      rwa [inv_inv, Subgroup.mem_subgroupOf] at this) haL, fun h => absurd
      (Subgroup.mem_subgroupOf.mp h) hyL⟩
  rwa [Subgroup.mem_subgroupOf] at h

variable [N.Normal]

end Dihedral

end Prop18Setup

end CFSG.CGT.PushingUpLit.SolKNA
