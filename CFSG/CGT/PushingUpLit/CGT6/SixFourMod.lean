module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourIdent
public import CFSG.CGT.PushingUpLit.CGT6.SixFourE9

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {Y R : Subgroup G} {T : Sylow 2 G}

omit [Finite G] in
theorem omegaOneCenterIn_comm (R : Subgroup G) (a b : ↥(omegaOneCenterIn R)) : a * b = b * a :=
  Subtype.ext ((mem_omegaOneCenterIn_iff.mp b.2).2.1 a (mem_omegaOneCenterIn_iff.mp a.2).1)

omit [Finite G] in
theorem omegaOneCenterIn_mul_self (R : Subgroup G) (v : ↥(omegaOneCenterIn R)) : v * v = 1 := by
  apply Subtype.ext
  show (v : G) * v = 1
  rw [← sq]
  exact (mem_omegaOneCenterIn_iff.mp v.2).2.2

namespace EightCtx

@[expose] noncomputable def vActG (h : EightCtx Y T R) : G →* MulAut ↥(omegaOneCenterIn R) :=
  @MulAut.conjNormal G _ (omegaOneCenterIn R) h.V_normal

theorem vActG_apply (h : EightCtx Y T R) (g : G) (v : ↥(omegaOneCenterIn R)) :
    ((h.vActG g v : ↥(omegaOneCenterIn R)) : G) = g * v * g⁻¹ :=
  @MulAut.conjNormal_apply G _ (omegaOneCenterIn R) h.V_normal g v

theorem R_le_ker_vActG (h : EightCtx Y T R) : R ≤ h.vActG.ker := by
  intro r hr
  rw [MonoidHom.mem_ker]
  ext v
  rw [vActG_apply]
  show r * (v : G) * r⁻¹ = v
  rw [(mem_omegaOneCenterIn_iff.mp v.2).2.1 r hr, mul_inv_cancel_right]

@[expose] noncomputable def vAct (h : EightCtx Y T R) [R.Normal] :
    G ⧸ R →* MulAut ↥(omegaOneCenterIn R) :=
  QuotientGroup.lift R h.vActG h.R_le_ker_vActG

theorem vAct_mk (h : EightCtx Y T R) [R.Normal] (g : G) (v : ↥(omegaOneCenterIn R)) :
    ((h.vAct (QuotientGroup.mk g) v : ↥(omegaOneCenterIn R)) : G) = g * v * g⁻¹ :=
  h.vActG_apply g v

@[expose] noncomputable def cV (h : EightCtx Y T R) [R.Normal] (S : Subgroup (G ⧸ R)) :
    Subgroup ↥(omegaOneCenterIn R) :=
  autFixGrp (S.map h.vAct)

theorem mem_cV (h : EightCtx Y T R) [R.Normal] {S : Subgroup (G ⧸ R)}
    {v : ↥(omegaOneCenterIn R)} : v ∈ h.cV S ↔ ∀ s ∈ S, h.vAct s v = v := by
  rw [cV, mem_autFixGrp]
  constructor
  · intro H s hs
    exact H _ ⟨s, hs, rfl⟩
  · rintro H _ ⟨s, hs, rfl⟩
    exact H s hs

theorem cV_mk_map (h : EightCtx Y T R) [R.Normal] (H : Subgroup G) :
    (h.cV (H.map (QuotientGroup.mk' R))).map (omegaOneCenterIn R).subtype =
      omegaOneCenterIn R ⊓ Subgroup.centralizer (H : Set G) := by
  ext g
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have := (h.mem_cV.mp hv) (QuotientGroup.mk' R x) ⟨x, hx, rfl⟩
    have h2 := congrArg Subtype.val this
    rw [QuotientGroup.mk'_apply, h.vAct_mk] at h2
    show x * (v : G) = v * x
    calc x * (v : G) = (x * v * x⁻¹) * x := by group
      _ = v * x := by rw [h2]
  · rintro ⟨hgV, hgC⟩
    refine ⟨⟨g, hgV⟩, h.mem_cV.mpr ?_, rfl⟩
    rintro _ ⟨x, hx, rfl⟩
    apply Subtype.ext
    rw [QuotientGroup.mk'_apply, h.vAct_mk]
    have := Subgroup.mem_centralizer_iff.mp hgC x hx
    show x * g * x⁻¹ = g
    rw [this]; group

theorem index_cV_mk_map_mul_card (h : EightCtx Y T R) [R.Normal] (H : Subgroup G) :
    (h.cV (H.map (QuotientGroup.mk' R))).index *
      Nat.card ↥(omegaOneCenterIn R ⊓ Subgroup.centralizer (H : Set G)) =
      Nat.card ↥(omegaOneCenterIn R) := by
  have hc : Nat.card ↥(h.cV (H.map (QuotientGroup.mk' R))) =
      Nat.card ↥(omegaOneCenterIn R ⊓ Subgroup.centralizer (H : Set G)) := by
    rw [← h.cV_mk_map H]
    exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
  rw [← hc, mul_comm]
  exact Subgroup.card_mul_index _

theorem cV_sup (h : EightCtx Y T R) [R.Normal] (S S' : Subgroup (G ⧸ R)) :
    h.cV (S ⊔ S') = h.cV S ⊓ h.cV S' := by
  ext v
  simp only [Subgroup.mem_inf, mem_cV]
  constructor
  · intro H
    exact ⟨fun s hs => H s (Subgroup.mem_sup_left hs), fun s hs => H s (Subgroup.mem_sup_right hs)⟩
  · rintro ⟨H1, H2⟩ s hs
    let F : Subgroup (G ⧸ R) := (MulAction.stabilizer (MulAut ↥(omegaOneCenterIn R)) v).comap h.vAct
    have hS : S ≤ F := fun s hs => by
      show h.vAct s • v = v
      exact H1 s hs
    have hS' : S' ≤ F := fun s hs => by
      show h.vAct s • v = v
      exact H2 s hs
    exact (sup_le hS hS') hs

theorem cV_conj (h : EightCtx Y T R) [R.Normal] (S : Subgroup (G ⧸ R)) (k : G ⧸ R) :
    h.cV (S.map (MulAut.conj k).toMonoidHom) =
      (h.cV S).comap (h.vAct k⁻¹ : MulAut ↥(omegaOneCenterIn R)).toMonoidHom := by
  ext v
  rw [Subgroup.mem_comap, mem_cV, mem_cV]
  constructor
  · intro H s hs
    have h1 := H (k * s * k⁻¹) ⟨s, hs, rfl⟩
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply] at h1
    have h2 := congrArg (fun w => h.vAct k⁻¹ w) h1
    simp only [← MulAut.mul_apply, ← map_mul] at h2
    simpa [MulAut.mul_apply] using h2
  · rintro H _ ⟨s, hs, rfl⟩
    have h1 : h.vAct s (h.vAct k⁻¹ v) = h.vAct k⁻¹ v := H s hs
    show h.vAct (k * s * k⁻¹) v = v
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, h1, ← MulAut.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, MulAut.one_apply]

theorem index_cV_conj (h : EightCtx Y T R) [R.Normal] (S : Subgroup (G ⧸ R)) (k : G ⧸ R) :
    (h.cV (S.map (MulAut.conj k).toMonoidHom)).index = (h.cV S).index := by
  rw [h.cV_conj S k]
  exact Subgroup.index_comap_of_surjective _ (MulEquiv.surjective _)

theorem index_cV_jBar (h : EightCtx Y T R) [R.Normal] {n : ℕ} (hn : 1 ≤ n)
    (hnat : IsNaturalSLTwoModule ↥Y n) : (h.cV (jBar R T)).index = 2 ^ n := by
  classical
  obtain ⟨A, hA, hnot, hJA, -⟩ := eight_sl_nine h hn hnat
  obtain ⟨𝔘, -, hmain⟩ := eight_sl_main h hn hnat
  obtain ⟨-, hrel, -, hwt, -⟩ := hmain A hA hnot
  have hAJ : A ≤ jIn (T : Subgroup G) := by
    rw [jIn_eq_thompsonJ]
    exact le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian (T : Subgroup G) A) => A) A hA
  have hCV : omegaOneCenterIn R ⊓ Subgroup.centralizer (jIn (T : Subgroup G) : Set G) =
      omegaOneCenterIn R ⊓ Subgroup.centralizer (A : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAJ))
    · intro v hv
      obtain ⟨hvV, hvA⟩ := Subgroup.mem_inf.mp hv
      refine Subgroup.mem_inf.mpr ⟨hvV, ?_⟩
      have hAR : A ⊔ R ≤ Subgroup.centralizer ({v} : Set G) := by
        refine sup_le ?_ ?_
        · intro a ha
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          rw [Set.mem_singleton_iff] at hw
          rw [hw]
          exact (Subgroup.mem_centralizer_iff.mp hvA a ha).symm
        · intro r hr
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          rw [Set.mem_singleton_iff] at hw
          rw [hw]
          exact ((mem_omegaOneCenterIn_iff.mp hvV).2.1 r hr).symm
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have := Subgroup.mem_centralizer_iff.mp (hAR (hJA hj)) v (Set.mem_singleton v)
      exact this.symm
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact GaloisField.card 2 n (by omega)
  have h2 : Nat.card ↥(omegaOneCenterIn R) =
      2 ^ n * Nat.card ↥(omegaOneCenterIn R ⊓ Subgroup.centralizer (A : Set G)) := by
    have := hwt
    unfold wtG at this
    rw [h.hC, hrel, hcard] at this
    exact this
  have h1 := h.index_cV_mk_map_mul_card (jIn (T : Subgroup G))
  have hpos : 0 < Nat.card ↥(omegaOneCenterIn R ⊓
      Subgroup.centralizer (jIn (T : Subgroup G) : Set G)) := Nat.card_pos
  rw [jBar]
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1, h2, hCV]

theorem le_index_autFixSub (h : EightCtx Y T R) [R.Normal] {n : ℕ}
    (φ : (↥Y ⧸ pCore 2 ↥Y) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (ψ : ↥(shortU ↥Y) →* Multiplicative (Fin 2 → GaloisField 2 n))
    (hψs : Function.Surjective ψ)
    (hψe : ∀ (l u : ↥Y) (hu : u ∈ shortU ↥Y) (hu' : l * u * l⁻¹ ∈ shortU ↥Y),
      ψ ⟨l * u * l⁻¹, hu'⟩ = Multiplicative.ofAdd
        ((φ (l : ↥Y ⧸ pCore 2 ↥Y) : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
          (Multiplicative.toAdd (ψ ⟨u, hu⟩))))
    (y : ↥Y)
    (hfix : ∀ w : Fin 2 → GaloisField 2 n,
      (φ (y : ↥Y ⧸ pCore 2 ↥Y) : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec w = w → w = 0) :
    Nat.card (GaloisField 2 n) ^ 2 ≤
      (autFixSub (h.vAct (QuotientGroup.mk (y : G)))).index := by
  classical
  have : (shortU ↥Y).Normal := by unfold shortU; infer_instance
  set σ : MulAut ↥(omegaOneCenterIn R) := h.vAct (QuotientGroup.mk (y : G)) with hσ
  have hσapp : ∀ v : ↥(omegaOneCenterIn R), ((σ v : ↥(omegaOneCenterIn R)) : G) = y * v * (y : G)⁻¹ :=
    fun v => h.vAct_mk (y : G) v
  let Φ : ↥(omegaOneCenterIn R) →* ↥(omegaOneCenterIn R) :=
    MonoidHom.mk' (fun v => σ v * v⁻¹) (fun a b => by
      simp only [map_mul, mul_inv_rev]
      have hc := omegaOneCenterIn_comm R
      calc σ a * σ b * (b⁻¹ * a⁻¹) = σ a * (σ b * b⁻¹) * a⁻¹ := by group
        _ = σ a * (a⁻¹ * (σ b * b⁻¹)) := by rw [mul_assoc, hc (σ b * b⁻¹) a⁻¹]
        _ = _ := by group)
  have hker : Φ.ker = autFixSub σ := by
    ext v
    rw [MonoidHom.mem_ker, mem_autFixSub]
    show σ v * v⁻¹ = 1 ↔ σ v = v
    exact mul_inv_eq_one
  rw [← hker, Subgroup.index_ker]
  have hUV : ∀ u : ↥(shortU ↥Y), ((blockUEquiv Y u : ↥(blockU Y)) : G) ∈ omegaOneCenterIn R :=
    fun u => h.blockU_le_V (blockUEquiv Y u).2
  let ι : ↥(shortU ↥Y) → ↥(omegaOneCenterIn R) := fun u => ⟨(blockUEquiv Y u : G), hUV u⟩
  have hιmul : ∀ a b : ↥(shortU ↥Y), ι (a * b) = ι a * ι b := fun a b => rfl
  have hιinj : Function.Injective ι := by
    intro a b hab
    have : ((ι a : ↥(omegaOneCenterIn R)) : G) = ((ι b : ↥(omegaOneCenterIn R)) : G) :=
      congrArg Subtype.val hab
    exact (blockUEquiv Y).injective (Subtype.ext this)
  set M : Matrix (Fin 2) (Fin 2) (GaloisField 2 n) :=
    (φ (y : ↥Y ⧸ pCore 2 ↥Y) : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) with hM
  have hinj : Function.Injective (fun w : Fin 2 → GaloisField 2 n => M.mulVec w - w) := by
    intro w w' hww'
    have h1 : M.mulVec (w - w') = w - w' := by
      have : M.mulVec w - w = M.mulVec w' - w' := hww'
      rw [Matrix.mulVec_sub]
      linear_combination this
    have := hfix _ h1
    exact sub_eq_zero.mp this
  have hsurj : Function.Surjective (fun w : Fin 2 → GaloisField 2 n => M.mulVec w - w) :=
    Finite.injective_iff_surjective.mp hinj
  have hex : ∀ t : Fin 2 → GaloisField 2 n, ∃ u : ↥(shortU ↥Y), ∃ hu' : y * (u : ↥Y) * y⁻¹ ∈ shortU ↥Y,
      ψ ⟨y * (u : ↥Y) * y⁻¹, hu'⟩ * (ψ u)⁻¹ = Multiplicative.ofAdd t := by
    intro t
    obtain ⟨w, hw⟩ := hsurj t
    obtain ⟨u, hu⟩ := hψs (Multiplicative.ofAdd w)
    have hu' : y * (u : ↥Y) * y⁻¹ ∈ shortU ↥Y := Subgroup.Normal.conj_mem inferInstance _ u.2 y
    refine ⟨u, hu', ?_⟩
    have := hψe y (u : ↥Y) u.2 hu'
    rw [show (⟨(u : ↥Y), u.2⟩ : ↥(shortU ↥Y)) = u from rfl] at this
    rw [this, hu]
    simp only [toAdd_ofAdd]
    rw [← ofAdd_neg, ← ofAdd_add]
    congr 1
    simpa [sub_eq_add_neg] using hw
  choose u hu' hu using hex
  let c : (Fin 2 → GaloisField 2 n) → ↥(shortU ↥Y) := fun t => ⟨y * (u t : ↥Y) * y⁻¹, hu' t⟩ * (u t)⁻¹
  have hψc : ∀ t, ψ (c t) = Multiplicative.ofAdd t := fun t => by
    rw [show c t = ⟨y * (u t : ↥Y) * y⁻¹, hu' t⟩ * (u t)⁻¹ from rfl, map_mul, map_inv]
    exact hu t
  have hΦc : ∀ t, Φ (ι (u t)) = ι (c t) := by
    intro t
    apply Subtype.ext
    show ((σ (ι (u t)) * (ι (u t))⁻¹ : ↥(omegaOneCenterIn R)) : G) = ((ι (c t) : ↥(omegaOneCenterIn R)) : G)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hσapp]
    show y * ((u t : ↥Y) : G) * (y : G)⁻¹ * ((u t : ↥Y) : G)⁻¹ = (((y * (u t : ↥Y) * y⁻¹ * (u t : ↥Y)⁻¹ : ↥Y)) : G)
    simp [mul_assoc]
  have hsinj : Function.Injective (fun t : Fin 2 → GaloisField 2 n =>
      (⟨Φ (ι (u t)), Φ.mem_range.mpr ⟨_, rfl⟩⟩ : Φ.range)) := by
    intro t t' htt'
    have h1 : Φ (ι (u t)) = Φ (ι (u t')) := congrArg Subtype.val htt'
    rw [hΦc, hΦc] at h1
    have h2 := hιinj h1
    have h3 : ψ (c t) = ψ (c t') := by rw [h2]
    rw [hψc, hψc] at h3
    exact Multiplicative.ofAdd.injective h3
  have := Nat.card_le_card_of_injective _ hsinj
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin] at this
  exact this

end EightCtx

end CFSG.CGT.PushingUpLit.CGT6
