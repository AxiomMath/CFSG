module

public import CFSG.ClassicalInvolution.Asc77.AscE189Model
public import CFSG.ClassicalInvolution.Asc77.AscIHHelp
public import CFSG.ClassicalInvolution.RouteD.GapsR2

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Helpers

variable {M Y : Type} [Group M] [Group Y]

theorem isUniqueInvolution_map_of_injOn (ψ : M →* Y) {F : Subgroup M} {z : M}
    (hinj : ∀ x ∈ F, ψ x = 1 → x = 1) (hz : IsUniqueInvolution F z) :
    IsUniqueInvolution (F.map ψ) (ψ z) where
  mem := Subgroup.mem_map_of_mem ψ hz.mem
  ne_one := fun h => hz.ne_one (hinj z hz.mem h)
  sq := by rw [← map_mul, hz.sq, map_one]
  unique := by
    rintro _ ⟨y, hy, rfl⟩ hy2
    have : y * y = 1 := hinj (y * y) (F.mul_mem hy hy) (by rw [map_mul]; exact hy2)
    rcases hz.unique y hy this with h | h
    · left
      rw [h, map_one]
    · right
      rw [h]

theorem injOn_conjSub (ψ : M →* Y) {F : Subgroup M} (hinj : ∀ x ∈ F, ψ x = 1 → x = 1) (y : M) :
    ∀ x ∈ conjSub y F, ψ x = 1 → x = 1 := by
  intro x hx h1
  rw [mem_conjSub_iff] at hx
  have h0 : ψ (y⁻¹ * x * y) = 1 := by
    rw [map_mul, map_mul, h1]
    simp
  have h2 := hinj _ hx h0
  have : x = y * (y⁻¹ * x * y) * y⁻¹ := by group
  rw [this, h2]
  group

omit [Group Y] in
theorem isSylow2In_map_of_injOn {Y' : Type} [Group Y'] (ψ : M →* Y') {F R : Subgroup M}
    (hinj : ∀ x ∈ F, ψ x = 1 → x = 1) (hR : IsSylow2In R F) :
    IsSylow2In (R.map ψ) (F.map ψ) := by
  refine ⟨Subgroup.map_mono hR.1, hR.2.1.map ψ, fun V hV hV2 hle => ?_⟩
  set V' : Subgroup M := F ⊓ V.comap ψ with hV'
  have hV'2 : IsPGroup 2 ↥V' := by
    intro x
    obtain ⟨k, hk⟩ := hV2 ⟨ψ x, x.2.2⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : ψ ((x : M) ^ 2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa [map_pow] using this
    have h2 := hinj _ (F.pow_mem x.2.1 _) h1
    simpa using h2
  have hRV' : R ≤ V' := fun r hr => ⟨hR.1 hr, hle (Subgroup.mem_map_of_mem ψ hr)⟩
  have hV'R : V' = R := hR.2.2 V' inf_le_left hV'2 hRV'
  refine le_antisymm (fun y hy => ?_) hle
  obtain ⟨x, hxF, rfl⟩ := hV hy
  have : x ∈ V' := ⟨hxF, hy⟩
  rw [hV'R] at this
  exact Subgroup.mem_map_of_mem ψ this

theorem map_conjSub_eq (ψ : M →* Y) (g : M) (R : Subgroup M) :
    (conjSub g R).map ψ = conjSub (ψ g) (R.map ψ) :=
  map_conj_eq_conjSub_map ψ g R

theorem conjSub_le_commutator {F : Subgroup M} (hperf : F ≤ ⁅F, F⁆) (y : M) :
    conjSub y F ≤ ⁅conjSub y F, conjSub y F⁆ := by
  have h := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) hperf
  rwa [Subgroup.map_commutator] at h

theorem isPerfect_of_le_commutator {F : Subgroup M} (h : F ≤ ⁅F, F⁆) : Group.IsPerfect ↥F :=
  Subgroup.isPerfect_iff.mpr (le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact F.mul_mem (F.mul_mem (F.mul_mem ha hb) (F.inv_mem ha)) (F.inv_mem hb)) h)

end Helpers

section Component

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y]

theorem e189_component (e : ℕ) (t : StatedLieTag) (n : ℕ) (hmodel : E189ModelAt p e t n)
    {Λ : Set (Subgroup Y)} (hΛ : ConjInvariant Λ)
    (ψ : ModelGrp p e t n →* Y) (hker : ψ.ker ≤ Subgroup.center (ModelGrp p e t n))
    {F₁ : Subgroup (ModelGrp p e t n)} (hF₁ : F₁ ∈ modelFund p e t n)
    (hinj : ∀ x ∈ F₁, ψ x = 1 → x = 1) (hperf : F₁ ≤ ⁅F₁, F₁⁆) (hK : F₁.map ψ ∈ Λ)
    {z₁ : ModelGrp p e t n} (hz₁ : IsUniqueInvolution F₁ z₁) (q : ModelGrp p e t n)
    (hzt : ψ z₁ * ψ (q * z₁ * q⁻¹) = ψ (q * z₁ * q⁻¹) * ψ z₁)
    (hat : ψ z₁ * ψ (q * z₁ * q⁻¹) ≠ 1)
    (hne : conjSub (ψ (q * z₁ * q⁻¹)) (F₁.map ψ) ≠ F₁.map ψ)
    (hcomm : Commutes (F₁.map ψ) (conjSub (ψ (q * z₁ * q⁻¹)) (F₁.map ψ)))
    (hnbΛ : ∀ L ∈ Λ, ((L = F₁.map ψ ∨ Commutes L (F₁.map ψ)) ↔
      (L = conjSub (ψ (q * z₁ * q⁻¹)) (F₁.map ψ) ∨
        Commutes L (conjSub (ψ (q * z₁ * q⁻¹)) (F₁.map ψ))))) :
    (∃ K'' ∈ twinSet Λ (F₁.map ψ), K'' ≠ F₁.map ψ ∧ ∃ R₁ R₂ : Subgroup Y,
        IsSylow2In R₁ (F₁.map ψ) ∧ IsSylow2In R₂ K'' ∧ Commutes R₁ R₂ ∧ ∃ u x : Y,
        u ∈ R₁ ⊔ R₂ ∧ u ≠ 1 ∧ u * u = 1 ∧ x * u * x⁻¹ = ψ z₁ * ψ (q * z₁ * q⁻¹)) ∨
    (∃ x : Y, ∃ M' ∈ twinSet Λ (conjSub x (F₁.map ψ)), M' ≠ conjSub x (F₁.map ψ) ∧
        ∀ w ∈ conjSub x (F₁.map ψ) ⊔ M', w * (ψ z₁ * ψ (q * z₁ * q⁻¹)) =
          (ψ z₁ * ψ (q * z₁ * q⁻¹)) * w) := by
  set t₁ := q * z₁ * q⁻¹ with ht₁
  have hperfF : Group.IsPerfect ↥F₁ := isPerfect_of_le_commutator hperf
  have h1 : ⁅z₁, t₁⁆ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hzt
  have h2 : z₁ * t₁ ∉ ψ.ker := fun h => hat (by rw [← map_mul]; exact h)
  have h3 : conjSub t₁ F₁ ≠ F₁ := by
    intro heq
    apply hne
    rw [← map_conjSub_eq, heq]
  have h4 : Commutes F₁ (conjSub t₁ F₁) :=
    RouteD.commutes_of_commutes_map ψ hker hperfF (by rw [map_conjSub_eq]; exact hcomm)
  have hzK : IsUniqueInvolution (F₁.map ψ) (ψ z₁) := isUniqueInvolution_map_of_injOn ψ hinj hz₁
  have hperf₂ : conjSub t₁ F₁ ≤ ⁅conjSub t₁ F₁, conjSub t₁ F₁⁆ := conjSub_le_commutator hperf t₁
  have h5 : ∀ S : Subgroup (ModelGrp p e t n), (∃ y, S = conjSub y F₁) →
      ((S = F₁ ∨ Commutes S F₁) ↔ (S = conjSub t₁ F₁ ∨ Commutes S (conjSub t₁ F₁))) := by
    rintro S ⟨y, rfl⟩
    have hperfS := conjSub_le_commutator hperf y
    have hSΛ : (conjSub y F₁).map ψ ∈ Λ := by
      rw [map_conjSub_eq]
      exact hΛ _ _ hK
    have hF₂map : (conjSub t₁ F₁).map ψ = conjSub (ψ t₁) (F₁.map ψ) := map_conjSub_eq ψ t₁ F₁
    have e1 : conjSub y F₁ = F₁ ↔ (conjSub y F₁).map ψ = F₁.map ψ :=
      ⟨fun h => by rw [h], fun h => RouteD.Gaps.eq_of_map_eq_of_central ψ hker hperfS hperf h⟩
    have e2 : conjSub y F₁ = conjSub t₁ F₁ ↔
        (conjSub y F₁).map ψ = conjSub (ψ t₁) (F₁.map ψ) :=
      ⟨fun h => by rw [h, hF₂map], fun h => RouteD.Gaps.eq_of_map_eq_of_central ψ hker hperfS hperf₂
        (h.trans hF₂map.symm)⟩
    have e3 : Commutes (conjSub y F₁) F₁ ↔ Commutes ((conjSub y F₁).map ψ) (F₁.map ψ) :=
      ⟨fun h => by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        rw [← map_mul, ← map_mul, h a ha b hb],
        fun h => RouteD.commutes_of_commutes_map ψ hker (isPerfect_of_le_commutator hperfS) h⟩
    have e4 : Commutes (conjSub y F₁) (conjSub t₁ F₁) ↔
        Commutes ((conjSub y F₁).map ψ) (conjSub (ψ t₁) (F₁.map ψ)) :=
      ⟨fun h => by
        rw [← hF₂map]
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        rw [← map_mul, ← map_mul, h a ha b hb],
        fun h => RouteD.commutes_of_commutes_map ψ hker (isPerfect_of_le_commutator hperfS)
          (by rw [hF₂map]; exact h)⟩
    rw [e1, e2, e3, e4]
    exact hnbΛ _ hSΛ
  rcases hmodel ψ.ker hker F₁ hF₁ z₁ hz₁ q h1 h2 h3 h4 h5 with
    ⟨F₃, -, hF₃ne, hF₁F₃, ⟨y, hy⟩, z₃, hz₃, hz₁z₃, R₁, R₃, hR₁, hR₃, u, x, hu, huN, hu2, hux⟩ |
    ⟨x, M₂, -, hM₂ne, -, ⟨y, hy⟩, z₂, hz₂, hxz, hw⟩
  · left
    subst hy
    have hinj₃ := injOn_conjSub ψ hinj y
    have hperf₃ := conjSub_le_commutator hperf y
    have hΛ₃ : (conjSub y F₁).map ψ ∈ Λ := by
      rw [map_conjSub_eq]
      exact hΛ _ _ hK
    have hz₃' : ψ z₃ = ψ z₁ := by
      have : ψ (z₁⁻¹ * z₃) = 1 := hz₁z₃
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this.symm
    refine ⟨(conjSub y F₁).map ψ, ⟨hΛ₃, ψ z₁, hzK, ?_⟩, ?_, R₁.map ψ, R₃.map ψ,
      isSylow2In_map_of_injOn ψ hinj hR₁, isSylow2In_map_of_injOn ψ hinj₃ hR₃, ?_, ψ u, ψ x, ?_,
      ?_, ?_, ?_⟩
    · rw [← hz₃']
      exact isUniqueInvolution_map_of_injOn ψ hinj₃ hz₃
    · intro h
      exact hF₃ne (RouteD.Gaps.eq_of_map_eq_of_central ψ hker hperf₃ hperf h)
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hF₁F₃ a (hR₁.1 ha) b (hR₃.1 hb)]
    · rw [← Subgroup.map_sup]
      exact Subgroup.mem_map_of_mem ψ hu
    · exact fun h => huN h
    · rw [← map_mul]
      exact (MonoidHom.mem_ker.mp hu2)
    · have h5 : ψ ((x * u * x⁻¹)⁻¹ * (z₁ * t₁)) = 1 := hux
      rw [map_mul, map_inv, inv_mul_eq_one, map_mul] at h5
      rw [← map_mul]
      simpa [map_mul, map_inv] using h5
  · right
    subst hy
    have hinj₂ := injOn_conjSub ψ hinj y
    have hperf₂ := conjSub_le_commutator hperf y
    have hΛ₂ : (conjSub y F₁).map ψ ∈ Λ := by
      rw [map_conjSub_eq]
      exact hΛ _ _ hK
    have hxK : IsUniqueInvolution (conjSub (ψ x) (F₁.map ψ)) (ψ x * ψ z₁ * (ψ x)⁻¹) := hzK.conj _
    have hz₂' : ψ z₂ = ψ x * ψ z₁ * (ψ x)⁻¹ := by
      have : ψ ((x * z₁ * x⁻¹)⁻¹ * z₂) = 1 := hxz
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      simpa [map_mul, map_inv] using this.symm
    have hxperf : conjSub x F₁ ≤ ⁅conjSub x F₁, conjSub x F₁⁆ := conjSub_le_commutator hperf x
    refine ⟨ψ x, (conjSub y F₁).map ψ, ⟨hΛ₂, ψ x * ψ z₁ * (ψ x)⁻¹, hxK, ?_⟩, ?_, ?_⟩
    · rw [← hz₂']
      exact isUniqueInvolution_map_of_injOn ψ hinj₂ hz₂
    · rw [← map_conjSub_eq]
      intro h
      exact hM₂ne (RouteD.Gaps.eq_of_map_eq_of_central ψ hker hperf₂ hxperf h)
    · intro w hw
      rw [← map_conjSub_eq, ← Subgroup.map_sup] at hw
      obtain ⟨w₀, hw₀, rfl⟩ := hw
      have h5 := MonoidHom.mem_ker.mp (hw w₀ hw₀)
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, map_mul] at h5
      exact h5

end Component

end CFSG.ClassicalInvolution.Asc77
