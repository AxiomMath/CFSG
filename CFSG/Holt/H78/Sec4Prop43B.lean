module

public import CFSG.Holt.H78.Sec4Prop43A
public import CFSG.Holt.H78.Sec4FinalA
public import CFSG.Holt.H78.Sec4KnownKV
public import CFSG.Holt.H78.Start

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

namespace HoltData

variable {K X : Type*} [Group K] [MulAction K X]

theorem coord_smul_eq_iff_of_conj (D : HoltData K X)
    (hO : jOddCore K X = ⊥) {g : K}
    {σ : D.ι ≃ D.ι} (hσ : ∀ i, D.L (σ i) = (D.L i).map (MulAut.conj g).toMonoidHom)
    (i : D.ι) (a b : X) :
    D.coord (g • a) (σ i) = D.coord (g • b) (σ i) ↔ D.coord a i = D.coord b i := by
  rw [D.coord_eq_iff_forall_mem_L, D.coord_eq_iff_forall_mem_L]
  simp only [orbit_jOddCore_eq_singleton hO, Set.mem_singleton_iff]
  have key : ∀ (l : K) (x : X), (g * l * g⁻¹) • g • x = g • x ↔ l • x = x := fun l x => by
    rw [← mul_smul, inv_mul_cancel_right, mul_smul, smul_left_cancel_iff]
  constructor
  · intro h l hl
    have hl' : g * (l : K) * g⁻¹ ∈ D.L (σ i) := by
      rw [hσ i]
      exact ⟨l, hl, rfl⟩
    have := h ⟨_, D.L_le _ hl'⟩ hl'
    simpa only [key] using this
  · intro h l hl
    have hl' := hl
    rw [hσ i] at hl'
    obtain ⟨l₀, hl₀, hl₀l⟩ := hl'
    have hl₀H : l₀ ∈ jHull K X := D.L_le i hl₀
    have := h ⟨l₀, hl₀H⟩ hl₀
    rw [← hl₀l]
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, key] using this

theorem mem_normalizer_L_of_conj (D : HoltData K X) {g : K} {σ : D.ι ≃ D.ι}
    (hσ : ∀ i, D.L (σ i) = (D.L i).map (MulAut.conj g).toMonoidHom) {k : D.ι}
    (hk : σ k = k) : g ∈ Subgroup.normalizer (D.L k : Set K) := by
  have h := hσ k
  rw [hk] at h
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [h]
    exact ⟨x, hx, rfl⟩
  · rw [h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : g * y * g⁻¹ = g * x * g⁻¹ := hyx
    rw [mul_left_inj, mul_right_inj] at hyx'
    exact hyx' ▸ hy

end HoltData

section Helpers

variable {K : Type*} [Group K]

theorem fusionIsSylowIn_inf_of_conj_mem' [Finite K] {p : ℕ} [Fact p.Prime] {S H N : Subgroup K}
    (hS : fusionIsSylowIn p S H) (hNH : N ≤ H) (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) :
    fusionIsSylowIn p (S ⊓ N) N := by
  refine ⟨inf_le_right, hS.2.1.to_le inf_le_left, fun P hPN hP hle => ?_⟩
  obtain ⟨R, hPR, hR⟩ := exists_fusionIsSylowIn_ge hP (hPN.trans hNH)
  obtain ⟨k, hk, hkR⟩ := exists_mem_conj_of_fusionIsSylowIn hS hR
  have hconj : ∀ x ∈ P, k⁻¹ * x * k ∈ S ⊓ N := fun x hx => ⟨(hkR x).mp (hPR hx), by
    simpa using hN k⁻¹ (inv_mem hk) x (hPN hx)⟩
  have hcard : Nat.card P ≤ Nat.card ↥(S ⊓ N) := Nat.card_le_card_of_injective
    (fun x : P => (⟨k⁻¹ * x * k, hconj x x.2⟩ : ↥(S ⊓ N))) (fun x y h => by
      have h' := congrArg Subtype.val h
      simp only [mul_left_inj, mul_right_inj] at h'
      exact Subtype.ext h')
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem fusionIsSylowIn_subgroupOf_top {p : ℕ} {S H : Subgroup K}
    (hS : fusionIsSylowIn p S H) : fusionIsSylowIn p (S.subgroupOf H) ⊤ := by
  refine ⟨le_top, hS.2.1.comap_of_injective H.subtype H.subtype_injective, fun Q _ hQ hSQ => ?_⟩
  have hQH : Q.map H.subtype ≤ H := Subgroup.map_subtype_le Q
  have h1 : S ≤ Q.map H.subtype := fun x hx => ⟨⟨x, hS.1 hx⟩, hSQ hx, rfl⟩
  have h2 := hS.2.2 _ hQH (hQ.map H.subtype) h1
  ext x
  constructor
  · intro hx
    have : (x : K) ∈ Q.map H.subtype := ⟨x, hx, rfl⟩
    rw [h2] at this
    exact this
  · intro hx
    exact hSQ hx

theorem mem_map_conj_iff {L : Subgroup K} {h x : K} :
    x ∈ L.map (MulAut.conj h).toMonoidHom ↔ h⁻¹ * x * h ∈ L := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨h⁻¹ * x * h, hx, by simp [mul_assoc]⟩

theorem conj_mem_normalizer_of_conj_eq {ι : Type*} {L : ι → Subgroup K} {h n : K}
    {σ : ι ≃ ι} (hσ : ∀ j, L (σ j) = (L j).map (MulAut.conj h).toMonoidHom)
    (hn : ∀ j, n ∈ Subgroup.normalizer (L j : Set K)) (k : ι) :
    h * n * h⁻¹ ∈ Subgroup.normalizer (L k : Set K) := by
  obtain ⟨j, rfl⟩ := σ.surjective k
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [hσ j, mem_map_conj_iff, mem_map_conj_iff]
  convert Subgroup.mem_normalizer_iff.mp (hn j) (h⁻¹ * x * h) using 2
  group

end Helpers

namespace AltConfig

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {α β : Ω} (C : AltConfig G Ω α β)

@[expose] noncomputable def coordEquiv : holtDelta G Ω α β ≃ ∀ i, C.D.Ψc i :=
  Equiv.ofBijective _ (C.D.coord_bijective C.oddCore_eq_bot)

@[simp] theorem coordEquiv_apply (δ : holtDelta G Ω α β) : C.coordEquiv δ = C.D.coord δ := rfl

@[simp] theorem coord_coordEquiv_symm (x : ∀ i, C.D.Ψc i) :
    C.D.coord (C.coordEquiv.symm x) = x :=
  C.coordEquiv.apply_symm_apply x

theorem eq_of_coord_eq {δ δ' : holtDelta G Ω α β} (h : C.D.coord δ = C.D.coord δ') : δ = δ' :=
  C.coordEquiv.injective h

@[expose] def hyper (i : C.D.ι) : Set Ω :=
  {ω | ∃ δ : holtDelta G Ω α β, (δ : Ω) = ω ∧ C.D.coord δ i = C.D.coord C.γ i}

theorem mem_hyper_iff {i : C.D.ι} (δ : holtDelta G Ω α β) :
    (δ : Ω) ∈ C.hyper i ↔ C.D.coord δ i = C.D.coord C.γ i :=
  ⟨fun ⟨δ', hδ', h⟩ => (Subtype.ext hδ' : δ' = δ) ▸ h, fun h => ⟨δ, rfl, h⟩⟩

@[expose] def kerC (i : C.D.ι) : Subgroup G :=
  stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G (C.hyper i)

theorem kerC_le_inf (i : C.D.ι) : C.kerC i ≤ stabilizer G α ⊓ stabilizer G β := inf_le_left

theorem kerC_le_stabilizer_pair (i : C.D.ι) : C.kerC i ≤ stabilizer G ({α, β} : Set Ω) :=
  (C.kerC_le_inf i).trans (stabilizer_inf_le_stabilizer_pair α β)

theorem smul_eq_of_mem_kerC {i : C.D.ι} {g : G} (hg : g ∈ C.kerC i) {δ : holtDelta G Ω α β}
    (hδ : C.D.coord δ i = C.D.coord C.γ i) : g • (δ : Ω) = δ :=
  (mem_fixingSubgroup_iff G).mp hg.2 _ ((C.mem_hyper_iff δ).mpr hδ)

theorem nontrivial_Ψc (i : C.D.ι) : Nontrivial (C.D.Ψc i) :=
  Fintype.one_lt_card_iff_nontrivial.mp (by have := C.D.five_le_card i; omega)

theorem twoPointElt_smul_of_mem_kerC {i : C.D.ι} {g : G} (hg : g ∈ C.kerC i)
    {δ : holtDelta G Ω α β} (hδ : C.D.coord δ i = C.D.coord C.γ i) :
    twoPointElt (C.kerC_le_stabilizer_pair i hg) • δ = δ :=
  Subtype.ext (C.smul_eq_of_mem_kerC hg hδ)

theorem exists_conj_L_eq_of_mem_kerC {i : C.D.ι} {g : G} (hg : g ∈ C.kerC i) :
    ∃ σ : C.D.ι ≃ C.D.ι, (∀ k, C.D.L (σ k) =
      (C.D.L k).map (MulAut.conj (twoPointElt (C.kerC_le_stabilizer_pair i hg))).toMonoidHom) ∧
        ∀ k, σ k = k := by
  obtain ⟨σ, hσ⟩ := C.D.conj_L (twoPointElt (C.kerC_le_stabilizer_pair i hg))
  have hσk : ∀ k, k ≠ i → σ k = k := by
    intro k hki
    by_contra hne
    have := C.nontrivial_Ψc k
    obtain ⟨c, hc⟩ := exists_ne (C.D.coord C.γ k)
    set y := C.coordEquiv.symm (Function.update (C.D.coord C.γ) k c)
    have hy : C.D.coord y = Function.update (C.D.coord C.γ) k c := C.coord_coordEquiv_symm _
    have h1 := C.D.coord_smul_eq_iff_of_conj C.oddCore_eq_bot hσ k C.γ y
    rw [C.twoPointElt_smul_of_mem_kerC hg rfl,
      C.twoPointElt_smul_of_mem_kerC hg (by rw [hy, Function.update_of_ne hki.symm]), hy,
      Function.update_self, Function.update_of_ne hne] at h1
    exact hc (h1.mp rfl).symm
  refine ⟨σ, hσ, fun k => ?_⟩
  by_cases hki : k = i
  · subst hki
    by_contra hne
    exact hne (σ.injective (hσk (σ k) hne))
  · exact hσk k hki

theorem twoPointElt_mem_normalizer_of_mem_kerC {i : C.D.ι} {g : G} (hg : g ∈ C.kerC i)
    (k : C.D.ι) : twoPointElt (C.kerC_le_stabilizer_pair i hg) ∈
      Subgroup.normalizer (C.D.L k : Set (twoPointSection G Ω α β)) := by
  obtain ⟨σ, hσ, hσid⟩ := C.exists_conj_L_eq_of_mem_kerC hg
  exact C.D.mem_normalizer_L_of_conj hσ (hσid k)

theorem coord_smul_eq_iff_of_mem_kerC {i : C.D.ι} {g : G} (hg : g ∈ C.kerC i) (k : C.D.ι)
    (a b : holtDelta G Ω α β) :
    C.D.coord (twoPointElt (C.kerC_le_stabilizer_pair i hg) • a) k =
        C.D.coord (twoPointElt (C.kerC_le_stabilizer_pair i hg) • b) k ↔
      C.D.coord a k = C.D.coord b k := by
  obtain ⟨σ, hσ, hσid⟩ := C.exists_conj_L_eq_of_mem_kerC hg
  have h := C.D.coord_smul_eq_iff_of_conj C.oddCore_eq_bot hσ k a b
  rwa [hσid k] at h

theorem coord_smul_of_mem_kerC {i : C.D.ι} {g : G} (hg : g ∈ C.kerC i)
    {δ δ' : holtDelta G Ω α β} (h : (δ' : Ω) = g • (δ : Ω)) {j : C.D.ι} (hj : j ≠ i) :
    C.D.coord δ' j = C.D.coord δ j := by
  have hδ' : δ' = twoPointElt (C.kerC_le_stabilizer_pair i hg) • δ := Subtype.ext h
  set δ₀ := C.coordEquiv.symm (Function.update (C.D.coord δ) i (C.D.coord C.γ i))
  have hδ₀ : C.D.coord δ₀ = Function.update (C.D.coord δ) i (C.D.coord C.γ i) :=
    C.coord_coordEquiv_symm _
  have hfix := C.twoPointElt_smul_of_mem_kerC hg (δ := δ₀) (by rw [hδ₀, Function.update_self])
  have h1 := (C.coord_smul_eq_iff_of_mem_kerC hg j δ δ₀).mpr
    (by rw [hδ₀, Function.update_of_ne hj])
  rw [hfix, hδ₀, Function.update_of_ne hj] at h1
  rw [hδ', h1]

@[expose] noncomputable def kerCElt (i : C.D.ι) :
    C.kerC i →* Subgroup.normalizer (C.D.L i : Set (twoPointSection G Ω α β)) :=
  (((twoPointHom G Ω α β).comp (Subgroup.inclusion (C.kerC_le_stabilizer_pair i))).codRestrict
    (twoPointSection G Ω α β) fun _ => twoPointHom_mem_twoPointSection _).codRestrict _
      fun g => C.twoPointElt_mem_normalizer_of_mem_kerC g.2 i

@[expose] noncomputable def kerCHom (i : C.D.ι) : C.kerC i →* Equiv.Perm (C.D.Ψc i) :=
  (C.D.nRho i).comp (C.kerCElt i)

theorem coord_smul_eq_kerCHom {i : C.D.ι} (g : C.kerC i) {δ δ' : holtDelta G Ω α β}
    (h : (δ' : Ω) = (g : G) • (δ : Ω)) : C.D.coord δ' i = C.kerCHom i g (C.D.coord δ i) := by
  have hδ' : δ' = (C.kerCElt i g : twoPointSection G Ω α β) • δ := Subtype.ext h
  rw [kerCHom, MonoidHom.comp_apply, C.D.nRho_coord, hδ']

theorem smul_eq_of_kerCHom_eq_one {i : C.D.ι} {g : C.kerC i} (hg : C.kerCHom i g = 1)
    (δ : holtDelta G Ω α β) : (g : G) • (δ : Ω) = δ := by
  have hmem : (g : G) • (δ : Ω) ∈ holtDelta G Ω α β := by
    have := (twoPointElt (C.kerC_le_stabilizer_pair i g.2) • δ).2
    exact this
  set δ' : holtDelta G Ω α β := ⟨_, hmem⟩
  have : δ' = δ := by
    refine C.eq_of_coord_eq (funext fun j => ?_)
    by_cases hj : j = i
    · subst hj
      rw [C.coord_smul_eq_kerCHom g rfl, hg, Equiv.Perm.one_apply]
    · exact C.coord_smul_of_mem_kerC g.2 rfl hj
  exact congrArg Subtype.val this

end AltConfig

section TwoPointElt

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {α β : Ω}

theorem twoPointElt_mul_mul_inv {g h k : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω))
    (hh : h ∈ stabilizer G ({α, β} : Set Ω)) (hk : k ∈ stabilizer G ({α, β} : Set Ω))
    (hghk : g * h * k⁻¹ ∈ stabilizer G ({α, β} : Set Ω)) :
    twoPointElt hghk = twoPointElt hg * twoPointElt hh * (twoPointElt hk)⁻¹ := by
  apply Subtype.ext
  change twoPointHom G Ω α β ⟨g * h * k⁻¹, hghk⟩ =
    twoPointHom G Ω α β ⟨g, hg⟩ * twoPointHom G Ω α β ⟨h, hh⟩ * (twoPointHom G Ω α β ⟨k, hk⟩)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem mem_twoPointNormalizer_iff_of_mem {L : Subgroup (twoPointSection G Ω α β)} {g : G}
    (hg : g ∈ stabilizer G ({α, β} : Set Ω)) :
    g ∈ twoPointNormalizer G Ω α β L ↔
      twoPointElt hg ∈ Subgroup.normalizer (L : Set (twoPointSection G Ω α β)) :=
  ⟨fun h => by obtain ⟨_, h⟩ := mem_twoPointNormalizer.mp h; exact h,
    fun h => mem_twoPointNormalizer.mpr ⟨hg, h⟩⟩

end TwoPointElt

namespace AltConfig

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {α β : Ω} (C : AltConfig G Ω α β)

abbrev calG : Subgroup G :=
  stabilizer G α ⊓ stabilizer G β ⊓ stabilizer G (C.γ : Ω) ⊓
    twoPointNormalizer G Ω α β (C.D.L C.i₁)

abbrev calP : Subgroup G := C.S ⊓ twoPointNormalizer G Ω α β (C.D.L C.i₁)

theorem calP_le_calG : C.calP ≤ C.calG := inf_le_inf_right _ C.sylow.1

theorem calG_le_inf : C.calG ≤ stabilizer G α ⊓ stabilizer G β := inf_le_left.trans inf_le_left

theorem calG_le_stabilizer_pair : C.calG ≤ stabilizer G ({α, β} : Set Ω) :=
  C.calG_le_inf.trans (stabilizer_inf_le_stabilizer_pair α β)

theorem calG_le_stabilizer_γ : C.calG ≤ stabilizer G (C.γ : Ω) := inf_le_left.trans inf_le_right

@[expose] def calK : Subgroup G := C.calG ⊓ ⨅ k, twoPointNormalizer G Ω α β (C.D.L k)

theorem calK_le_calG : C.calK ≤ C.calG := inf_le_left

theorem mem_normalizer_of_mem_calK {g : G} (hg : g ∈ C.calK) (k : C.D.ι) :
    twoPointElt (C.calG_le_stabilizer_pair (C.calK_le_calG hg)) ∈
      Subgroup.normalizer (C.D.L k : Set (twoPointSection G Ω α β)) :=
  (mem_twoPointNormalizer_iff_of_mem _).mp (Subgroup.mem_iInf.mp hg.2 k)

theorem conj_mem_calK {h n : G} (hh : h ∈ C.calG) (hn : n ∈ C.calK) : h * n * h⁻¹ ∈ C.calK := by
  have hnG := C.calK_le_calG hn
  refine Subgroup.mem_inf.mpr ⟨C.calG.mul_mem (C.calG.mul_mem hh hnG) (C.calG.inv_mem hh),
    Subgroup.mem_iInf.mpr fun k => ?_⟩
  have h1 := C.calG_le_stabilizer_pair hh
  have h2 := C.calG_le_stabilizer_pair hnG
  have h3 : h * n * h⁻¹ ∈ stabilizer G ({α, β} : Set Ω) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) (Subgroup.inv_mem _ h1)
  rw [mem_twoPointNormalizer_iff_of_mem h3, twoPointElt_mul_mul_inv h1 h2 h1]
  obtain ⟨σ, hσ⟩ := C.D.conj_L (twoPointElt h1)
  exact conj_mem_normalizer_of_conj_eq hσ (C.mem_normalizer_of_mem_calK hn) k

theorem kerC_le_calG (i : C.D.ι) : C.kerC i ≤ C.calG := fun _ hg =>
  ⟨⟨C.kerC_le_inf i hg, C.smul_eq_of_mem_kerC hg rfl⟩,
    (mem_twoPointNormalizer_iff_of_mem (C.kerC_le_stabilizer_pair i hg)).mpr
      (C.twoPointElt_mem_normalizer_of_mem_kerC hg C.i₁)⟩

theorem kerC_le_calK (i : C.D.ι) : C.kerC i ≤ C.calK := fun _ hg =>
  ⟨C.kerC_le_calG i hg, Subgroup.mem_iInf.mpr fun k =>
    (mem_twoPointNormalizer_iff_of_mem (C.kerC_le_stabilizer_pair i hg)).mpr
      (C.twoPointElt_mem_normalizer_of_mem_kerC hg k)⟩

theorem conj_mem_kerC {i : C.D.ι} {h n : G} (hh : h ∈ C.calK) (hn : n ∈ C.kerC i) :
    h * n * h⁻¹ ∈ C.kerC i := by
  have hhG := C.calK_le_calG hh
  have hinv : h⁻¹ ∈ C.calK := C.calK.inv_mem hh
  change h * n * h⁻¹ ∈ stabilizer G α ⊓ stabilizer G β ⊓ fixingSubgroup G (C.hyper i)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact (stabilizer G α ⊓ stabilizer G β).mul_mem
      ((stabilizer G α ⊓ stabilizer G β).mul_mem (C.calG_le_inf hhG) (C.kerC_le_inf i hn))
      ((stabilizer G α ⊓ stabilizer G β).inv_mem (C.calG_le_inf hhG))
  · rw [mem_fixingSubgroup_iff]
    rintro _ ⟨δ, rfl, hδ⟩
    have hinvG := C.calK_le_calG hinv
    set π := twoPointElt (C.calG_le_stabilizer_pair hinvG)
    have hπN := C.mem_normalizer_of_mem_calK hinv i
    have hπγ : π • C.γ = C.γ := Subtype.ext (C.calG_le_stabilizer_γ hinvG)
    have h1 := ((C.D.normalizer_L_preserves_fibres hπN δ C.γ).1).mpr hδ
    rw [hπγ] at h1
    have h2 : n • ((π • δ : holtDelta G Ω α β) : Ω) = (π • δ : holtDelta G Ω α β) :=
      C.smul_eq_of_mem_kerC hn h1
    change n • (h⁻¹ • (δ : Ω)) = h⁻¹ • (δ : Ω) at h2
    rw [mul_smul, mul_smul, h2, smul_inv_smul]

variable [Finite G]

theorem fusionIsSylowIn_calK (hP : fusionIsSylowIn 2 C.calP C.calG) :
    fusionIsSylowIn 2 (C.calP ⊓ C.calK) C.calK :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  fusionIsSylowIn_inf_of_conj_mem' hP C.calK_le_calG fun _ hh _ hn => C.conj_mem_calK hh hn

theorem fusionIsSylowIn_kerC (hP : fusionIsSylowIn 2 C.calP C.calG) (i : C.D.ι) :
    fusionIsSylowIn 2 (C.calP ⊓ C.kerC i) (C.kerC i) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := fusionIsSylowIn_inf_of_conj_mem' (C.fusionIsSylowIn_calK hP) (C.kerC_le_calK i)
    fun _ hh _ hn => C.conj_mem_kerC hh hn
  rwa [inf_assoc, inf_eq_right.mpr (C.kerC_le_calK i)] at h

omit [Finite G] in
theorem kerCHom_apply_γ {i : C.D.ι} (g : C.kerC i) :
    C.kerCHom i g (C.D.coord C.γ i) = C.D.coord C.γ i :=
  (C.coord_smul_eq_kerCHom g (C.smul_eq_of_mem_kerC g.2 rfl).symm).symm

@[expose] noncomputable def Qimg (i : C.D.ι) : Subgroup (Equiv.Perm (C.D.Ψc i)) :=
  ((C.calP ⊓ C.kerC i).subgroupOf (C.kerC i)).map (C.kerCHom i)

omit [Finite G] in
theorem Qimg_le_stabilizer (i : C.D.ι) :
    C.Qimg i ≤ stabilizer (Equiv.Perm (C.D.Ψc i)) (C.D.coord C.γ i) := by
  rintro _ ⟨g, -, rfl⟩
  exact C.kerCHom_apply_γ g

omit [Finite G] in
theorem isPGroup_Qimg (i : C.D.ι) : IsPGroup 2 (C.Qimg i) :=
  ((C.sylow.2.1.to_le inf_le_left).comap_of_injective (C.kerC i).subtype
    (C.kerC i).subtype_injective |>.to_le (by
      intro x hx
      exact hx.1)).map _

variable [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω]

omit [FaithfulSMul G Ω] in
theorem exists_kerCHom_eq (hS : Sec4Setting G Ω) {i : C.D.ι} {a : Equiv.Perm (C.D.Ψc i)}
    (ha : a ∈ alternatingGroup (C.D.Ψc i)) (haγ : a (C.D.coord C.γ i) = C.D.coord C.γ i) :
    ∃ g : C.kerC i, C.kerCHom i g = a := by
  have haM : a ∈ C.D.M i := by
    rw [HoltData.M, C.alt i]
    exact ha
  obtain ⟨h, hhL, hha⟩ := C.D.mem_M.mp haM
  have h1 : ((h : twoPointSection G Ω α β) : Equiv.Perm (holtDelta G Ω α β)) ∈
      ⁅twoPointJ G Ω α β, twoPointJ G Ω α β⁆ := by
    have hmap : (C.D.L i).map (twoPointSection G Ω α β).subtype ≤ twoPointJ G Ω α β := by
      rw [hS.twoPointJ_eq_map_jHull]
      exact Subgroup.map_mono (C.D.L_le i)
    have h2 : ((h : twoPointSection G Ω α β) : Equiv.Perm (holtDelta G Ω α β)) ∈
        (⁅C.D.L i, C.D.L i⁆).map (twoPointSection G Ω α β).subtype := by
      rw [HoltData.commutator_L_eq C.D C.oddCore_eq_bot i]
      exact ⟨h, hhL, rfl⟩
    rw [Subgroup.map_commutator] at h2
    exact Subgroup.commutator_mono hmap hmap h2
  obtain ⟨g, -, hgα, hgβ, hgδ⟩ := mem_twoPointJFix.mp (commutator_twoPointJ_le α β h1)
  have hcoordi : ∀ δ : holtDelta G Ω α β,
      C.D.coord ((h : twoPointSection G Ω α β) • δ) i = a (C.D.coord δ i) := fun δ => by
    rw [C.D.coord_smul, hha]
  have hcoordj : ∀ (δ : holtDelta G Ω α β) (j : C.D.ι), j ≠ i →
      C.D.coord ((h : twoPointSection G Ω α β) • δ) j = C.D.coord δ j := fun δ j hj => by
    rw [C.D.coord_smul, C.D.rho_eq_one_of_mem_L (Ne.symm hj) hhL, Equiv.Perm.one_apply]
  have hgK : g ∈ C.kerC i := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hgα, hgβ⟩, ?_⟩
    rw [mem_fixingSubgroup_iff]
    rintro _ ⟨δ, rfl, hδ⟩
    have : (h : twoPointSection G Ω α β) • δ = δ := by
      refine C.eq_of_coord_eq (funext fun j => ?_)
      by_cases hj : j = i
      · subst hj
        rw [hcoordi, hδ, haγ]
      · exact hcoordj δ j hj
    rw [← hgδ δ]
    exact congrArg Subtype.val this
  refine ⟨⟨g, hgK⟩, Equiv.ext fun c => ?_⟩
  set δ := C.coordEquiv.symm (Function.update (C.D.coord C.γ) i c)
  have hδ : C.D.coord δ i = c := by
    rw [C.coord_coordEquiv_symm, Function.update_self]
  have h3 := C.coord_smul_eq_kerCHom (δ := δ) (δ' := (h : twoPointSection G Ω α β) • δ)
    ⟨g, hgK⟩ (hgδ δ)
  rw [hcoordi, hδ] at h3
  exact h3.symm

omit [FaithfulSMul G Ω] in
theorem fusionIsSylowIn_Qimg_inf (hS : Sec4Setting G Ω) (hP : fusionIsSylowIn 2 C.calP C.calG)
    (i : C.D.ι) :
    fusionIsSylowIn 2 (C.Qimg i ⊓ alternatingGroup (C.D.Ψc i))
      (alternatingGroup (C.D.Ψc i) ⊓ stabilizer (Equiv.Perm (C.D.Ψc i)) (C.D.coord C.γ i)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := fusionIsSylowIn_map (C.kerCHom i)
    (fusionIsSylowIn_subgroupOf_top (C.fusionIsSylowIn_kerC hP i))
  have hle : alternatingGroup (C.D.Ψc i) ⊓ stabilizer (Equiv.Perm (C.D.Ψc i)) (C.D.coord C.γ i) ≤
      (⊤ : Subgroup (C.kerC i)).map (C.kerCHom i) := by
    rintro a ⟨ha, haγ⟩
    obtain ⟨g, hg⟩ := C.exists_kerCHom_eq hS ha haγ
    exact ⟨g, trivial, hg⟩
  have h2 := fusionIsSylowIn_inf_of_conj_mem' h1 hle (by
    intro x hx n hn
    obtain ⟨g, -, rfl⟩ := hx
    obtain ⟨hnA, hnγ⟩ := Subgroup.mem_inf.mp hn
    refine Subgroup.mem_inf.mpr ⟨(inferInstance : (alternatingGroup (C.D.Ψc i)).Normal).conj_mem
      n hnA _, ?_⟩
    change (C.kerCHom i g * n * (C.kerCHom i g)⁻¹) (C.D.coord C.γ i) = C.D.coord C.γ i
    have hn' : n (C.D.coord C.γ i) = C.D.coord C.γ i := hnγ
    have hg' := C.kerCHom_apply_γ g
    simp only [Equiv.Perm.mul_apply]
    rw [Equiv.Perm.inv_eq_iff_eq.mpr hg'.symm, hn', hg'])
  have h3 : C.Qimg i ⊓ (alternatingGroup (C.D.Ψc i) ⊓
      stabilizer (Equiv.Perm (C.D.Ψc i)) (C.D.coord C.γ i)) =
        C.Qimg i ⊓ alternatingGroup (C.D.Ψc i) := by
    rw [← inf_assoc, inf_right_comm, inf_eq_left.mpr (C.Qimg_le_stabilizer i)]
  rw [← h3]
  exact h2

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem eq_one_of_smul_eq_of_odd (hT : Odd (Nat.card (twoPointKernel G Ω α β)))
    {A : Subgroup G} (hA : IsPGroup 2 A) {g : G} (hgA : g ∈ A)
    (hgαβ : g ∈ stabilizer G α ⊓ stabilizer G β) (hgΔ : ∀ δ : holtDelta G Ω α β, g • (δ : Ω) = δ) :
    g = 1 := by
  have hgK : g ∈ twoPointKernel G Ω α β :=
    mem_twoPointKernel.mpr ⟨hgαβ.1, hgαβ.2, fun δ hδ => hgΔ ⟨δ, hδ⟩⟩
  obtain ⟨k, hk⟩ := hA ⟨g, hgA⟩
  have hk' : g ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  have h1 : orderOf g ∣ Nat.card (twoPointKernel G Ω α β) :=
    Subgroup.orderOf_dvd_natCard (twoPointKernel G Ω α β) hgK
  rw [hm] at h1
  rcases m with _ | m
  · rw [pow_zero, orderOf_eq_one_iff] at hm
    exact hm
  · have h2 := Nat.dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero m)) h1
    have h3 := Nat.odd_iff.mp hT
    omega

@[expose] def boxSet (Λc : ∀ i, Set (C.D.Ψc i)) : Set Ω :=
  {ω | ∃ δ : holtDelta G Ω α β, (δ : Ω) = ω ∧ ∀ i, C.D.coord δ i ∈ Λc i}

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_boxSet_iff {Λc : ∀ i, Set (C.D.Ψc i)} (δ : holtDelta G Ω α β) :
    (δ : Ω) ∈ C.boxSet Λc ↔ ∀ i, C.D.coord δ i ∈ Λc i :=
  ⟨fun ⟨δ', hδ', h⟩ => (Subtype.ext hδ' : δ' = δ) ▸ h, fun h => ⟨δ, rfl, h⟩⟩

theorem four_le_card_fixSet_of_stab_box (hS : Sec4Setting G Ω) (hαβ : α ≠ β) {P' : Subgroup G}
    (hP' : IsPGroup 2 P') (hP'G : P' ≤ C.calG) (Λc : ∀ i, Set (C.D.Ψc i))
    (hstab : ∀ p ∈ P', ∀ δ δ' : holtDelta G Ω α β, (δ' : Ω) = p • (δ : Ω) →
      (∀ i, C.D.coord δ i ∈ Λc i) → ∀ i, C.D.coord δ' i ∈ Λc i)
    (hmove : ∀ δ : holtDelta G Ω α β, ¬ (∀ i, C.D.coord δ i ∈ Λc i) → ∃ v ∈ P',
      (∀ δ' : holtDelta G Ω α β, (∀ i, C.D.coord δ' i ∈ Λc i) → v • (δ' : Ω) = δ') ∧
        v • (δ : Ω) ≠ δ)
    (hne : ∃ δ : holtDelta G Ω α β, ¬ ∀ i, C.D.coord δ i ∈ Λc i)
    (hsize : ∀ i, (Λc i).ncard = 1 ∨ 5 ≤ (Λc i).ncard) (h₁ : 5 ≤ (Λc C.i₁).ncard)
    (hj : ∃ j, j ≠ C.i₁ ∧ 5 ≤ (Λc j).ncard) : 4 ≤ Nat.card (fixSet Ω P') := by
  set V := P' ⊓ fixingSubgroup G (C.boxSet Λc) with hVdef
  have hV : IsPGroup 2 V := hP'.to_le inf_le_left
  have hVfix : ∀ v ∈ V, ∀ δ : holtDelta G Ω α β, (∀ i, C.D.coord δ i ∈ Λc i) →
      v • (δ : Ω) = δ := fun v hv δ hδ =>
    (mem_fixingSubgroup_iff G).mp (Subgroup.mem_inf.mp hv).2 _ ((C.mem_boxSet_iff δ).mpr hδ)
  have hmemV : ∀ v ∈ P', (∀ δ' : holtDelta G Ω α β, (∀ i, C.D.coord δ' i ∈ Λc i) →
      v • (δ' : Ω) = δ') → v ∈ V := fun v hv hfix => Subgroup.mem_inf.mpr ⟨hv,
    (mem_fixingSubgroup_iff G).mpr fun _ ⟨δ, hδ, hδΛ⟩ => hδ ▸ hfix δ hδΛ⟩
  have hV1 : V ≠ ⊥ := by
    obtain ⟨δ, hδ⟩ := hne
    obtain ⟨v, hv, hfix, hmv⟩ := hmove δ hδ
    intro hbot
    have : v ∈ V := hmemV v hv hfix
    rw [hbot, Subgroup.mem_bot] at this
    exact hmv (by rw [this, one_smul])
  have hVαβ : V ≤ stabilizer G α ⊓ stabilizer G β := inf_le_left.trans (hP'G.trans C.calG_le_inf)
  have hconj : ∀ p ∈ P', ∀ v ∈ V, p * v * p⁻¹ ∈ V := by
    intro p hp v hv
    refine hmemV _ (P'.mul_mem (P'.mul_mem hp (Subgroup.mem_inf.mp hv).1) (P'.inv_mem hp))
      fun δ hδ => ?_
    have hpinv := C.calG_le_stabilizer_pair (hP'G (P'.inv_mem hp))
    set δ'' := twoPointElt hpinv • δ
    have hδ'' : ∀ i, C.D.coord δ'' i ∈ Λc i := hstab _ (P'.inv_mem hp) δ δ'' rfl hδ
    have h1 : v • ((δ'' : holtDelta G Ω α β) : Ω) = δ'' := hVfix v hv δ'' hδ''
    change v • (p⁻¹ • (δ : Ω)) = p⁻¹ • (δ : Ω) at h1
    rw [mul_smul, mul_smul, h1, smul_inv_smul]
  have hPV : P' ≤ Subgroup.normalizer (V : Set G) := fun p hp =>
    Subgroup.mem_normalizer_iff.mpr fun v => ⟨fun hv => hconj p hp v hv, fun hv => by
      have := hconj p⁻¹ (P'.inv_mem hp) _ hv
      simpa [mul_assoc] using this⟩
  have hbox : ∀ δ : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω V ↔ ∀ i, C.D.coord δ i ∈ Λc i := by
    intro δ
    refine ⟨fun hδ => ?_, fun hδ v hv => hVfix v hv δ hδ⟩
    by_contra hnot
    obtain ⟨v, hv, hfix, hmv⟩ := hmove δ hnot
    exact hmv (hδ v (hmemV v hv hfix))
  exact C.four_le_card_fixSet_of_box hS hαβ hP' hP'G hV hV1 hVαβ hPV Λc hbox hsize h₁ hj

@[expose] def MapsDir (g : G) (j k : C.D.ι) : Prop :=
  ∀ δ₁ δ₂ δ₁' δ₂' : holtDelta G Ω α β, (δ₁' : Ω) = g • (δ₁ : Ω) → (δ₂' : Ω) = g • (δ₂ : Ω) →
    (C.D.coord δ₁' k = C.D.coord δ₂' k ↔ C.D.coord δ₁ j = C.D.coord δ₂ j)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mapsDir_one (j : C.D.ι) : C.MapsDir 1 j j := by
  intro δ₁ δ₂ δ₁' δ₂' h₁ h₂
  rw [one_smul] at h₁ h₂
  rw [(Subtype.ext h₁ : δ₁' = δ₁), (Subtype.ext h₂ : δ₂' = δ₂)]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem MapsDir.mul {g h : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω)) {j k l : C.D.ι}
    (h₁ : C.MapsDir g j k) (h₂ : C.MapsDir h k l) : C.MapsDir (h * g) j l := by
  intro δ₁ δ₂ δ₁'' δ₂'' e₁ e₂
  rw [h₂ (twoPointElt hg • δ₁) (twoPointElt hg • δ₂) δ₁'' δ₂'' (by rw [e₁, mul_smul]; rfl)
    (by rw [e₂, mul_smul]; rfl)]
  exact h₁ δ₁ δ₂ _ _ rfl rfl

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem MapsDir.inv {g : G} {j k : C.D.ι} (h : C.MapsDir g j k) : C.MapsDir g⁻¹ k j := by
  intro δ₁ δ₂ δ₁' δ₂' e₁ e₂
  refine (h δ₁' δ₂' δ₁ δ₂ ?_ ?_).symm
  · rw [e₁, smul_inv_smul]
  · rw [e₂, smul_inv_smul]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_mapsDir {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω)) :
    ∃ σ : C.D.ι ≃ C.D.ι, ∀ j, C.MapsDir g j (σ j) := by
  obtain ⟨σ, hσ⟩ := C.D.conj_L (twoPointElt hg)
  refine ⟨σ, fun j δ₁ δ₂ δ₁' δ₂' e₁ e₂ => ?_⟩
  rw [(Subtype.ext e₁ : δ₁' = twoPointElt hg • δ₁), (Subtype.ext e₂ : δ₂' = twoPointElt hg • δ₂)]
  exact C.D.coord_smul_eq_iff_of_conj C.oddCore_eq_bot hσ j δ₁ δ₂

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem MapsDir.eq_of_forall {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω))
    {σ : C.D.ι ≃ C.D.ι} (hσ : ∀ j, C.MapsDir g j (σ j)) {j k : C.D.ι} (h : C.MapsDir g j k) :
    k = σ j := by
  by_contra hk
  set m := σ.symm k
  have hm : m ≠ j := fun hmj => hk (by rw [← hmj, Equiv.apply_symm_apply])
  have hmk : C.MapsDir g m k := by
    have := hσ m
    rwa [Equiv.apply_symm_apply] at this
  have := C.nontrivial_Ψc j
  obtain ⟨c, hc⟩ := exists_ne (C.D.coord C.γ j)
  set δ := C.coordEquiv.symm (Function.update (C.D.coord C.γ) j c)
  have hδ : C.D.coord δ = Function.update (C.D.coord C.γ) j c := C.coord_coordEquiv_symm _
  have h1 := (hmk C.γ δ (twoPointElt hg • C.γ) (twoPointElt hg • δ) rfl rfl).mpr
    (by rw [hδ, Function.update_of_ne hm])
  have h2 := (h C.γ δ (twoPointElt hg • C.γ) (twoPointElt hg • δ) rfl rfl).mp h1
  rw [hδ, Function.update_self] at h2
  exact hc h2.symm

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem MapsDir.eq {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω)) {j k k' : C.D.ι}
    (h : C.MapsDir g j k) (h' : C.MapsDir g j k') : k = k' := by
  obtain ⟨σ, hσ⟩ := C.exists_mapsDir hg
  rw [MapsDir.eq_of_forall C hg hσ h, MapsDir.eq_of_forall C hg hσ h']

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mapsDir_i₁ {g : G} (hg : g ∈ twoPointNormalizer G Ω α β (C.D.L C.i₁)) :
    C.MapsDir g C.i₁ C.i₁ := by
  obtain ⟨hg', hN⟩ := mem_twoPointNormalizer.mp hg
  intro δ₁ δ₂ δ₁' δ₂' e₁ e₂
  rw [(Subtype.ext e₁ : δ₁' = twoPointElt hg' • δ₁), (Subtype.ext e₂ : δ₂' = twoPointElt hg' • δ₂)]
  exact (C.D.normalizer_L_preserves_fibres hN δ₁ δ₂).1

end AltConfig

end CFSG.Holt.H78
