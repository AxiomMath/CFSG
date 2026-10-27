module

public import CFSG.CGT.PushingUpLit.A78.Hyg
public import CFSG.CGT.PushingUpLit.A78.JStructure
public import CFSG.CGT.PushingUpLit.A78Sp4.Data

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

section ElemAbelian

variable {G : Type} [Group G]

theorem elemAb2_of_isElemAbelian {E : Subgroup G} (h : CFSG.Open.IsElemAbelian 2 E) :
    ElemAb2 E := by
  obtain ⟨hc, hs⟩ := h
  intro x hx y hy
  refine ⟨?_, ?_⟩
  · have := hc.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩
    exact congrArg Subtype.val this
  · have := hs x hx
    rwa [pow_two] at this

end ElemAbelian

section Helpers

variable {Γ : Type} [Group Γ] {L V : Subgroup Γ}

theorem exists_mul_of_mem_sup (hL : ∀ l ∈ L, ∀ v ∈ V, l * v * l⁻¹ ∈ V) {g : Γ}
    (hg : g ∈ L ⊔ V) : ∃ v ∈ V, ∃ l ∈ L, g = v * l := by
  rw [sup_comm] at hg
  exact (mem_sup_iff_of_normalizes hL).1 hg

theorem conj_eq_of_mul_comm {v l u : Γ} (h : v * (l * u * l⁻¹) = (l * u * l⁻¹) * v) :
    v * l * u * (v * l)⁻¹ = l * u * l⁻¹ :=
  calc v * l * u * (v * l)⁻¹ = v * (l * u * l⁻¹) * v⁻¹ := by group
    _ = (l * u * l⁻¹) * v * v⁻¹ := by rw [h]
    _ = l * u * l⁻¹ := by group

theorem relIndex_sup_of_le_normalizer {A B : Subgroup Γ}
    (hB : B ≤ Subgroup.normalizer (A : Set Γ)) : A.relIndex (B ⊔ A) = A.relIndex B := by
  have hN : (A.subgroupOf (B ⊔ A)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2
      (sup_le hB Subgroup.le_normalizer)
  have h1 := Subgroup.relIndex_sup_right (B.subgroupOf (B ⊔ A)) (A.subgroupOf (B ⊔ A))
  rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
    Subgroup.relIndex_subgroupOf (le_refl (B ⊔ A)), Subgroup.relIndex_subgroupOf le_sup_left] at h1
  exact h1

theorem eq_of_pow_mul_odd {a b m n : ℕ} (hm : Odd m) (hn : Odd n) (h : 2 ^ a * m = 2 ^ b * n) :
    a = b := by
  have h1 : 2 ^ a ∣ 2 ^ b := by
    have : 2 ^ a ∣ 2 ^ b * n := h ▸ dvd_mul_right _ _
    exact (Nat.Coprime.pow_left a (Nat.coprime_two_left.2 hn)).dvd_of_dvd_mul_right this
  have h2 : 2 ^ b ∣ 2 ^ a := by
    have : 2 ^ b ∣ 2 ^ a * m := h.symm ▸ dvd_mul_right _ _
    exact (Nat.Coprime.pow_left b (Nat.coprime_two_left.2 hm)).dvd_of_dvd_mul_right this
  exact Nat.pow_right_injective le_rfl (Nat.dvd_antisymm h1 h2)

theorem exists_hom_extension {S : Type} [Group S] [Finite S]
    (hL : ∀ l ∈ L, ∀ v ∈ V, l * v * l⁻¹ ∈ V) (hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    {φ' : ↥(L ⊔ V) →* S} (hs' : Function.Surjective φ') (hk' : φ'.ker = V.subgroupOf (L ⊔ V))
    {φ : ↥L →* S} (hs : Function.Surjective φ)
    (hk : φ.ker = (L ⊓ Subgroup.centralizer (V : Set Γ)).subgroupOf L) :
    L ⊓ Subgroup.centralizer (V : Set Γ) = L ⊓ V ∧
      ∃ φt : ↥(L ⊔ V) →* S, Function.Surjective φt ∧ φt.ker = V.subgroupOf (L ⊔ V) ∧
        ∀ (l : Γ) (hl : l ∈ L), φt ⟨l, Subgroup.mem_sup_left hl⟩ = φ ⟨l, hl⟩ := by
  have hVker : ∀ (v : Γ) (hv : v ∈ V), φ' ⟨v, Subgroup.mem_sup_right hv⟩ = 1 := fun v hv => by
    have : (⟨v, Subgroup.mem_sup_right hv⟩ : ↥(L ⊔ V)) ∈ φ'.ker := by
      rw [hk']
      exact hv
    exact this
  let φL : ↥L →* S := φ'.comp (Subgroup.inclusion le_sup_left)
  have hφL : ∀ (l : Γ) (hl : l ∈ L), φL ⟨l, hl⟩ = φ' ⟨l, Subgroup.mem_sup_left hl⟩ := fun _ _ => rfl
  have hφLs : Function.Surjective φL := by
    intro s
    obtain ⟨g, rfl⟩ := hs' s
    obtain ⟨v, hv, l, hl, hg⟩ := exists_mul_of_mem_sup hL g.2
    refine ⟨⟨l, hl⟩, ?_⟩
    have : g = ⟨v, Subgroup.mem_sup_right hv⟩ * ⟨l, Subgroup.mem_sup_left hl⟩ := Subtype.ext hg
    rw [hφL, this, map_mul, hVker v hv, one_mul]
  have hker_le : φL.ker ≤ φ.ker := by
    intro x hx
    rw [hk, Subgroup.mem_subgroupOf]
    have h1 : φ' ⟨(x : Γ), Subgroup.mem_sup_left x.2⟩ = 1 := hx
    have h2 : (⟨(x : Γ), Subgroup.mem_sup_left x.2⟩ : ↥(L ⊔ V)) ∈ V.subgroupOf (L ⊔ V) := by
      rw [← hk']
      exact h1
    exact ⟨x.2, Subgroup.mem_centralizer_iff.2 fun y hy => hV y hy x h2⟩
  let α : S →* S := (MonoidHom.liftOfSurjective φL hφLs) ⟨φ, hker_le⟩
  have hα : ∀ x : ↥L, α (φL x) = φ x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply φL _ (Function.rightInverse_surjInv hφLs)
      ⟨φ, hker_le⟩ x
  have hαs : Function.Surjective α := by
    intro s
    obtain ⟨x, rfl⟩ := hs s
    exact ⟨φL x, hα x⟩
  have hαi : Function.Injective α := Finite.injective_iff_surjective.2 hαs
  have hinf : L ⊓ Subgroup.centralizer (V : Set Γ) = L ⊓ V := by
    apply le_antisymm
    · rintro x ⟨hxL, hxC⟩
      refine ⟨hxL, ?_⟩
      have h1 : φ ⟨x, hxL⟩ = 1 := by
        have : (⟨x, hxL⟩ : ↥L) ∈ φ.ker := by
          rw [hk]
          exact ⟨hxL, hxC⟩
        exact this
      have h2 : φL ⟨x, hxL⟩ = 1 := hαi (by rw [hα, h1, map_one])
      have h3 : (⟨x, Subgroup.mem_sup_left hxL⟩ : ↥(L ⊔ V)) ∈ φ'.ker := h2
      rw [hk'] at h3
      exact h3
    · rintro x ⟨hxL, hxV⟩
      exact ⟨hxL, Subgroup.mem_centralizer_iff.2 fun y hy => hV y hy x hxV⟩
  refine ⟨hinf, α.comp φ', hαs.comp hs', ?_, ?_⟩
  · ext g
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, map_eq_one_iff α hαi, ← MonoidHom.mem_ker, hk']
  · intro l hl
    exact hα ⟨l, hl⟩

end Helpers

section Commutator

variable {G : Type} [Group G] [Finite G] {L V : Subgroup G} {n : ℕ}

theorem card_commutator_ge_of_natSL (hn : n ≠ 0)
    {φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    {ψ : ↥V →* Multiplicative (Fin 2 → GaloisField 2 n)} (hψs : Function.Surjective ψ)
    (hψc : ∀ (l : ↥L) (v : ↥V) (hv : (l : G) * v * (l : G)⁻¹ ∈ V),
      ψ ⟨(l : G) * v * (l : G)⁻¹, hv⟩ = Multiplicative.ofAdd
        ((φ l : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (Multiplicative.toAdd (ψ v))))
    (hL : ∀ l ∈ L, ∀ v ∈ V, l * v * l⁻¹ ∈ V) {a l : G} (hl : l ∈ L)
    (hact : ∀ v ∈ V, a * v * a⁻¹ = l * v * l⁻¹) (hne : φ ⟨l, hl⟩ ≠ 1) :
    2 ^ n ≤ Nat.card ↥⁅V, Subgroup.zpowers a⁆ := by
  obtain ⟨w, hw⟩ : ∃ w : Fin 2 → GaloisField 2 n,
      (φ ⟨l, hl⟩ : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w ≠ w := by
    by_contra hcon
    exact hne (T2K.NatData.eq_one_of_forall_mulVec fun w => not_not.1 fun hw => hcon ⟨w, hw⟩)
  have hy : w - (φ ⟨l, hl⟩ : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w ≠ 0 :=
    sub_ne_zero.2 (Ne.symm hw)
  choose s hs using fun c : GaloisField 2 n => hψs (Multiplicative.ofAdd (c • w))
  have hcomm : ∀ v : ↥V, ⁅(v : G), a⁆ = (v : G) * (l * (v : G)⁻¹ * l⁻¹) := by
    intro v
    rw [← hact _ (inv_mem v.2), commutatorElement_def]
    group
  have hmem : ∀ v : ↥V, ⁅(v : G), a⁆ ∈ V := fun v => by
    rw [hcomm]
    exact mul_mem v.2 (hL l hl _ (inv_mem v.2))
  have hform : ∀ v : ↥V, Multiplicative.toAdd (ψ ⟨⁅(v : G), a⁆, hmem v⟩) =
      Multiplicative.toAdd (ψ v) - (φ ⟨l, hl⟩ : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
        (Multiplicative.toAdd (ψ v)) := by
    intro v
    have hv : l * ((v⁻¹ : ↥V) : G) * l⁻¹ ∈ V := hL l hl _ (v⁻¹).2
    have e : (⟨⁅(v : G), a⁆, hmem v⟩ : ↥V) = v * ⟨l * ((v⁻¹ : ↥V) : G) * l⁻¹, hv⟩ :=
      Subtype.ext (hcomm v)
    rw [e, map_mul, hψc ⟨l, hl⟩ v⁻¹ hv, map_inv, toAdd_mul, toAdd_ofAdd, toAdd_inv,
      Matrix.mulVec_neg, sub_eq_add_neg]
  refine (GaloisField.card 2 n hn).ge.trans (Nat.card_le_card_of_injective
    (fun c => ⟨⁅((s c : ↥V) : G), a⁆,
      Subgroup.commutator_mem_commutator (s c).2 (Subgroup.mem_zpowers a)⟩) fun c c' hcc => ?_)
  have h0 := congrArg Subtype.val hcc
  have e : (⟨_, hmem (s c)⟩ : ↥V) = ⟨_, hmem (s c')⟩ := Subtype.ext h0
  have h1 := hform (s c)
  rw [e, hform (s c'), hs, hs, toAdd_ofAdd, toAdd_ofAdd, Matrix.mulVec_smul,
    Matrix.mulVec_smul, ← smul_sub, ← smul_sub] at h1
  exact (smul_left_injective (GaloisField 2 n) hy h1).symm

end Commutator

section Side

variable {G : Type} [Group G] [Finite G] {L T J : Subgroup G} {e : ℕ}

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Side.conj_V (h : A78Side G L T J e) {g : G}
    (hg : g ∈ L ⊔ T) {v : G} (hv : v ∈ oTwoIn (L ⊔ T)) : g * v * g⁻¹ ∈ oTwoIn (L ⊔ T) :=
  (Subgroup.mem_normalizer_iff.1 (h.sup_le_normalizer_V hg) v).1 hv

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Side.conj_V_L (h : A78Side G L T J e) :
    ∀ l ∈ L, ∀ v ∈ oTwoIn (L ⊔ T), l * v * l⁻¹ ∈ oTwoIn (L ⊔ T) :=
  fun _ hl _ hv => h.conj_V (Subgroup.mem_sup_left hl) hv

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Side.comm_V (h : A78Side G L T J e) :
    ∀ x ∈ oTwoIn (L ⊔ T), ∀ y ∈ oTwoIn (L ⊔ T), x * y = y * x :=
  fun x hx y hy => (elemAb2_of_isElemAbelian h.elem x hx y hy).1

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Side.inf_V_eq_centralizer
    (h : A78Side G L T J e) :
    L ⊓ oTwoIn (L ⊔ T) = L ⊓ Subgroup.centralizer (oTwoIn (L ⊔ T) : Set G) := by
  obtain ⟨φ', hs', hk'⟩ := h.quot
  obtain ⟨φ, ψ, hs, hk, -⟩ := h.nat
  exact (exists_hom_extension h.conj_V_L h.comm_V hs' hk' hs hk).1.symm

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Side.sup_inf_centralizer_V
    (h : A78Side G L T J e) :
    (L ⊔ oTwoIn (L ⊔ T)) ⊓ Subgroup.centralizer (oTwoIn (L ⊔ T) : Set G) = oTwoIn (L ⊔ T) := by
  apply le_antisymm
  · rintro g ⟨hg, hgC⟩
    obtain ⟨v, hv, l, hl, rfl⟩ := exists_mul_of_mem_sup h.conj_V_L hg
    have hvC : v⁻¹ ∈ Subgroup.centralizer (oTwoIn (L ⊔ T) : Set G) :=
      inv_mem (Subgroup.mem_centralizer_iff.2 fun y hy => h.comm_V y hy v hv)
    have hlC : l ∈ Subgroup.centralizer (oTwoIn (L ⊔ T) : Set G) := by
      have := mul_mem hvC hgC
      rwa [inv_mul_cancel_left] at this
    have hlV : l ∈ L ⊓ oTwoIn (L ⊔ T) := by
      rw [h.inf_V_eq_centralizer]
      exact ⟨hl, hlC⟩
    exact mul_mem hv hlV.2
  · intro v hv
    exact ⟨Subgroup.mem_sup_right hv,
      Subgroup.mem_centralizer_iff.2 fun y hy => h.comm_V y hy v hv⟩

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Side.inf_centralizer_sup_V
    (h : A78Side G L T J e) :
    oTwoIn (L ⊔ T) ⊓ Subgroup.centralizer ((L ⊔ oTwoIn (L ⊔ T) : Subgroup G) : Set G) =
      oTwoIn (L ⊔ T) ⊓ Subgroup.centralizer (L : Set G) := by
  ext x
  constructor
  · rintro ⟨hxV, hxC⟩
    exact ⟨hxV, Subgroup.centralizer_le (fun y hy => Subgroup.mem_sup_left hy) hxC⟩
  · rintro ⟨hxV, hxC⟩
    refine ⟨hxV, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    obtain ⟨v, hv, l, hl, rfl⟩ := exists_mul_of_mem_sup h.conj_V_L hg
    have h1 := h.comm_V v hv x hxV
    have h2 := Subgroup.mem_centralizer_iff.1 hxC l hl
    calc v * l * x = v * (l * x) := mul_assoc _ _ _
      _ = v * (x * l) := by rw [h2]
      _ = (v * x) * l := (mul_assoc _ _ _).symm
      _ = (x * v) * l := by rw [h1]
      _ = x * (v * l) := mul_assoc _ _ _

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Side.isNatSL_sup (h : A78Side G L T J e) :
    IsNatSL (L ⊔ oTwoIn (L ⊔ T)) (oTwoIn (L ⊔ T)) e := by
  obtain ⟨φ', hs', hk'⟩ := h.quot
  obtain ⟨φ, ψ, hs, hk, hψs, hψk, hψc⟩ := h.nat
  obtain ⟨-, φt, hts, htk, htl⟩ := exists_hom_extension h.conj_V_L h.comm_V hs' hk' hs hk
  refine ⟨φt, ψ, hts, ?_, hψs, ?_, ?_⟩
  · rw [htk, h.sup_inf_centralizer_V]
  · rw [h.inf_centralizer_sup_V]
    exact hψk
  · intro g w hw
    obtain ⟨v, hv, l, hl, hg⟩ := exists_mul_of_mem_sup h.conj_V_L g.2
    have hlw : l * (w : G) * l⁻¹ ∈ oTwoIn (L ⊔ T) := h.conj_V_L l hl w w.2
    have hgw : (g : G) * w * (g : G)⁻¹ = l * w * l⁻¹ := by
      rw [hg]
      exact conj_eq_of_mul_comm (h.comm_V v hv _ hlw)
    have e1 : (⟨(g : G) * w * (g : G)⁻¹, hw⟩ : ↥(oTwoIn (L ⊔ T))) = ⟨l * w * l⁻¹, hlw⟩ :=
      Subtype.ext hgw
    have e2 : φt g = φ ⟨l, hl⟩ := by
      have hgv : g = ⟨v, Subgroup.mem_sup_right hv⟩ * ⟨l, Subgroup.mem_sup_left hl⟩ :=
        Subtype.ext hg
      have hv1 : φt ⟨v, Subgroup.mem_sup_right hv⟩ = 1 := by
        have : (⟨v, Subgroup.mem_sup_right hv⟩ : ↥(L ⊔ oTwoIn (L ⊔ T))) ∈ φt.ker := by
          rw [htk]
          exact hv
        exact this
      rw [hgv, map_mul, hv1, one_mul]
      exact htl l hl
    rw [e1, e2]
    exact hψc ⟨l, hl⟩ w hlw

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Side.relIndex_J (h : A78Side G L T J e)
    (hVJ : oTwoIn (L ⊔ T) ≤ J) (he : e ≠ 0) : (oTwoIn (L ⊔ T)).relIndex J = 2 ^ e := by
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφs, hφk⟩ := h.quot
  have hJK : J ≤ L ⊔ oTwoIn (L ⊔ T) := h.sylowJ.le
  have hVK : (oTwoIn (L ⊔ T)).relIndex (L ⊔ oTwoIn (L ⊔ T)) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) := by
    unfold Subgroup.relIndex
    rw [← hφk, Subgroup.index_ker, MonoidHom.range_eq_top.2 hφs, Subgroup.card_top]
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) =
      2 ^ e * ((2 ^ e) ^ 2 - 1) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, GaloisField.card 2 e he]
  have hodd1 : Odd ((2 ^ e) ^ 2 - 1) := by
    have h4 : Even ((2 ^ e) ^ 2) := by
      rw [← pow_mul]
      exact Nat.even_pow.2 ⟨even_two, by omega⟩
    obtain ⟨k, hk⟩ := h4
    have : 0 < (2 ^ e) ^ 2 := by positivity
    exact ⟨k - 1, by omega⟩
  have hodd2 : Odd (J.relIndex (L ⊔ oTwoIn (L ⊔ T))) :=
    Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (CFSG.ABGLocalTools.isSylowOf_iff.1 h.sylowJ).2.2)
  have hmul := Subgroup.relIndex_mul_relIndex (oTwoIn (L ⊔ T)) J (L ⊔ oTwoIn (L ⊔ T)) hVJ hJK
  obtain ⟨k, hk⟩ := h.sylowJ.isPGroup.exists_card_eq
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (hk ▸ Subgroup.relIndex_dvd_card (oTwoIn (L ⊔ T)) J)
  rw [ha, hVK, hSL] at hmul
  rw [ha, eq_of_pow_mul_odd hodd2 hodd1 hmul]

end Side

section Cfg

variable {G : Type} [Group G] [Finite G] {L₁ L₂ T : Subgroup G} {e : ℕ}

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.relIndex_J_V₁ (h : A78Cfg G L₁ L₂ T e) :
    (oTwoIn (L₁ ⊔ T)).relIndex (oTwoIn (L₁ ⊔ T) ⊔ oTwoIn (L₂ ⊔ T)) = 2 ^ e :=
  h.side₁.relIndex_J le_sup_left (by have := h.two_le; omega)

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.relIndex_J_V₂ (h : A78Cfg G L₁ L₂ T e) :
    (oTwoIn (L₂ ⊔ T)).relIndex (oTwoIn (L₁ ⊔ T) ⊔ oTwoIn (L₂ ⊔ T)) = 2 ^ e :=
  h.side₂.relIndex_J le_sup_right (by have := h.two_le; omega)

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.index_V₁ (h : A78Cfg G L₁ L₂ T e) :
    (oTwoIn (L₁ ⊔ T) ⊓ oTwoIn (L₂ ⊔ T)).relIndex (oTwoIn (L₁ ⊔ T)) = 2 ^ e := by
  have h1 := relIndex_sup_of_le_normalizer (A := oTwoIn (L₂ ⊔ T)) (B := oTwoIn (L₁ ⊔ T))
    fun x hx => h.hyg.sup₂ (Subgroup.mem_sup_right (h.hyg.V₁_le hx))
  rw [Subgroup.inf_relIndex_left, ← h1]
  exact h.relIndex_J_V₂

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.index_V₂ (h : A78Cfg G L₁ L₂ T e) :
    (oTwoIn (L₁ ⊔ T) ⊓ oTwoIn (L₂ ⊔ T)).relIndex (oTwoIn (L₂ ⊔ T)) = 2 ^ e := by
  have h1 := relIndex_sup_of_le_normalizer (A := oTwoIn (L₁ ⊔ T)) (B := oTwoIn (L₂ ⊔ T))
    fun x hx => h.hyg.sup₁ (Subgroup.mem_sup_right (h.hyg.V₂_le hx))
  rw [Subgroup.inf_relIndex_right, ← h1, sup_comm (oTwoIn (L₂ ⊔ T)) (oTwoIn (L₁ ⊔ T))]
  exact h.relIndex_J_V₁

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.comm_ge (h : A78Cfg G L₁ L₂ T e) :
    ∀ v₂ ∈ oTwoIn (L₂ ⊔ T), v₂ ∉ oTwoIn (L₁ ⊔ T) →
      2 ^ e ≤ Nat.card ↥⁅oTwoIn (L₁ ⊔ T), Subgroup.zpowers v₂⁆ := by
  intro v₂ hv₂ hv₂V
  have he : e ≠ 0 := by
    have := h.two_le
    omega
  have hL := h.side₁.conj_V_L
  have hJ : v₂ ∈ L₁ ⊔ oTwoIn (L₁ ⊔ T) := h.side₁.sylowJ.le (Subgroup.mem_sup_right hv₂)
  obtain ⟨v, hv, l, hl, hvl⟩ := exists_mul_of_mem_sup hL hJ
  obtain ⟨φ, ψ, -, hk, hψs, -, hψc⟩ := h.side₁.nat
  have hact : ∀ u ∈ oTwoIn (L₁ ⊔ T), v₂ * u * v₂⁻¹ = l * u * l⁻¹ := by
    intro u hu
    rw [hvl]
    exact conj_eq_of_mul_comm (h.side₁.comm_V v hv _ (hL l hl u hu))
  have hne : φ ⟨l, hl⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨l, hl⟩ : ↥L₁) ∈ φ.ker := h1
    rw [hk, Subgroup.mem_subgroupOf] at h2
    have h3 : l ∈ L₁ ⊓ oTwoIn (L₁ ⊔ T) := by
      rw [h.side₁.inf_V_eq_centralizer]
      exact h2
    apply hv₂V
    rw [hvl]
    exact mul_mem hv h3.2
  exact card_commutator_ge_of_natSL he hψs hψc hL hl hact hne

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Cfg.jStructure (h : A78Cfg G L₁ L₂ T e) :
    JStructure G (oTwoIn (L₁ ⊔ T) ⊔ oTwoIn (L₂ ⊔ T)) (oTwoIn (L₁ ⊔ T)) (oTwoIn (L₂ ⊔ T)) e where
  two_le := h.two_le
  sup_eq := rfl
  conj_V := fun _ hj _ hx => h.side₁.conj_V (Subgroup.mem_sup_right (h.hyg.J_le hj)) hx
  conj_V₂ := fun _ hj _ hx => h.side₂.conj_V (Subgroup.mem_sup_right (h.hyg.J_le hj)) hx
  abelian_V := fun x hx y hy => h.side₁.comm_V x hx y hy
  sq_V := fun x hx => (elemAb2_of_isElemAbelian h.side₁.elem x hx x hx).2
  abelian_V₂ := fun x hx y hy => h.side₂.comm_V x hx y hy
  sq_V₂ := fun x hx => (elemAb2_of_isElemAbelian h.side₂.elem x hx x hx).2
  index_V := h.index_V₁
  index_V₂ := h.index_V₂
  comm_ge := h.comm_ge

end Cfg

end CFSG.CGT.PushingUpLit.A78Sp4
