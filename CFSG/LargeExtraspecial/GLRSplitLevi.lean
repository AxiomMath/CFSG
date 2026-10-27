module

public import CFSG.LargeExtraspecial.GLRSplitDemp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith

variable {G : Type*} [Group G] [Finite G] {S : Setting G} (C : Config S)

theorem mem_normalizer_of_forall_conj_mem {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  let f : H → H := fun x => ⟨g * x * g⁻¹, h x x.2⟩
  have hf : Function.Injective f := fun a b hab => Subtype.ext (by
    have := congrArg Subtype.val hab
    simpa [f] using this)
  obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hf) ⟨g * y * g⁻¹, hy⟩
  have : (x : G) = y := by
    have := congrArg Subtype.val hx
    simpa [f] using this
  exact this ▸ x.2

namespace Config

@[expose] def IsZCompl (H : Subgroup G) : Prop :=
  H ≤ C.A ∧ S.z ∉ H ∧ ∀ a ∈ C.A, a ∈ H ∨ a * S.z ∈ H

variable {C}

theorem IsZCompl.mem_iff_not {H : Subgroup G} (hH : C.IsZCompl H) {a : G} (ha : a ∈ C.A) :
    a * S.z ∈ H ↔ a ∉ H := by
  refine ⟨fun h1 h2 => hH.2.1 ?_, fun h => (hH.2.2 a ha).resolve_left h⟩
  have := H.mul_mem (H.inv_mem h2) h1
  rwa [inv_mul_cancel_left] at this

variable (C)

theorem exists_isZCompl : ∃ H : Subgroup G, C.IsZCompl H := by
  classical
  obtain ⟨H, hH⟩ := Set.Finite.exists_maximal (s := {H : Subgroup G | H ≤ C.A ∧ S.z ∉ H})
    (Set.toFinite _) ⟨⊥, bot_le, fun h => S.z_ne_one ((mem_bot).mp h)⟩
  refine ⟨H, hH.1.1, hH.1.2, fun a ha => ?_⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨haH, hazH⟩ := hcon
  have hcommA : ∀ x ∈ C.A, x * a = a * x := fun x hx => C.A_comm hx ha
  let H₁ : Subgroup G :=
    { carrier := {g | g ∈ H ∨ g * a ∈ H}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        rintro g g' (hg | hg) (hg' | hg')
        · exact Or.inl (H.mul_mem hg hg')
        · exact Or.inr (by rw [mul_assoc]; exact H.mul_mem hg hg')
        · right
          have hg'A : g' ∈ C.A := hH.1.1 hg'
          rw [mul_assoc, hcommA g' hg'A, ← mul_assoc]
          exact H.mul_mem hg hg'
        · left
          have hgA : g ∈ C.A := by
            have := C.A.mul_mem (hH.1.1 hg) (C.A.inv_mem ha)
            rwa [mul_inv_cancel_right] at this
          have hg'A : g' ∈ C.A := by
            have := C.A.mul_mem (hH.1.1 hg') (C.A.inv_mem ha)
            rwa [mul_inv_cancel_right] at this
          have : g * g' = (g * a) * (g' * a) := by
            rw [mul_assoc g a, ← mul_assoc a g' a, ← hcommA g' hg'A, mul_assoc g' a a,
              C.A_mul_self ha, mul_one]
          rw [this]
          exact H.mul_mem hg hg'
      inv_mem' := by
        rintro g (hg | hg)
        · exact Or.inl (H.inv_mem hg)
        · right
          have hgA : g ∈ C.A := by
            have := C.A.mul_mem (hH.1.1 hg) (C.A.inv_mem ha)
            rwa [mul_inv_cancel_right] at this
          have : g⁻¹ * a = (g * a)⁻¹ := by
            rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (C.A_mul_self ha)]
            exact hcommA _ (C.A.inv_mem hgA)
          rw [this]
          exact H.inv_mem hg }
  have hH₁A : H₁ ≤ C.A := by
    rintro g (hg | hg)
    · exact hH.1.1 hg
    · have := C.A.mul_mem (hH.1.1 hg) (C.A.inv_mem ha)
      rwa [mul_inv_cancel_right] at this
  have hle : H ≤ H₁ := fun g hg => Or.inl hg
  have haH₁ : a ∈ H₁ := Or.inr (by rw [C.A_mul_self ha]; exact H.one_mem)
  have hzH₁ : S.z ∈ H₁ := by
    by_contra hz
    have := hH.2 ⟨hH₁A, hz⟩ hle haH₁
    exact haH this
  rcases hzH₁ with hz | hz
  · exact hH.1.2 hz
  · apply hazH
    rw [S.z_comm (S.QG_le_M (C.A_le_QG ha))]
    exact hz

open Classical in
@[expose] noncomputable def chi (H : Subgroup G) (a : G) : ZMod 2 := if a ∈ H then 0 else 1

variable {C}

theorem chi_mul {H : Subgroup G} (hH : C.IsZCompl H) {a a' : G} (ha : a ∈ C.A)
    (ha' : a' ∈ C.A) : chi H (a * a') = chi H a + chi H a' := by
  classical
  have hzc : ∀ g ∈ C.A, g * S.z = S.z * g := fun g hg => S.z_comm (S.QG_le_M (C.A_le_QG hg))
  by_cases h1 : a ∈ H <;> by_cases h2 : a' ∈ H
  · simp [chi, h1, h2, H.mul_mem h1 h2]
  · have : a * a' ∉ H := fun h => h2 (by simpa using H.mul_mem (H.inv_mem h1) h)
    simp [chi, h1, h2, this]
  · have : a * a' ∉ H := fun h => h1 (by simpa using H.mul_mem h (H.inv_mem h2))
    simp [chi, h1, h2, this]
  · have h1' := (hH.mem_iff_not ha).mpr h1
    have h2' := (hH.mem_iff_not ha').mpr h2
    have : a * a' ∈ H := by
      have := H.mul_mem h1' h2'
      rwa [hzc a' ha', ← mul_assoc, mul_assoc a S.z S.z, S.z_mul_z, mul_one] at this
    simp only [chi, h1, h2, this, ↓reduceIte]
    decide

theorem chi_mul_z {H : Subgroup G} (hH : C.IsZCompl H) {a : G} (ha : a ∈ C.A) :
    chi H (a * S.z) = chi H a + 1 := by
  classical
  by_cases h1 : a ∈ H
  · have : a * S.z ∉ H := fun h => (hH.mem_iff_not ha).mp h h1
    simp [chi, h1, this]
  · have : a * S.z ∈ H := (hH.mem_iff_not ha).mpr h1
    simp only [chi, h1, this, ↓reduceIte]
    decide

theorem chi_eq_of_cl_eq {H H' : Subgroup G} (hH : C.IsZCompl H) (hH' : C.IsZCompl H')
    {a a' : G} (ha : a ∈ C.A) (ha' : a' ∈ C.A) (h : S.cl a = S.cl a') :
    chi H a + chi H' a = chi H a' + chi H' a' := by
  rcases (S.cl_eq_cl_iff ha.1 ha'.1).mp h with rfl | rfl
  · rfl
  · rw [chi_mul_z hH ha, chi_mul_z hH' ha]
    generalize chi H a = x
    generalize chi H' a = y
    revert x y
    decide

theorem exists_mem_B_conj {H H' : Subgroup G} (hH : C.IsZCompl H) (hH' : C.IsZCompl H') :
    ∃ q ∈ C.B, ∀ h ∈ H, q * h * q⁻¹ ∈ H' := by
  classical
  let lift : S.Qt → G := fun v => Classical.choose (S.exists_cl v)
  have hlift : ∀ v, lift v ∈ S.QG ∧ S.cl (lift v) = v := fun v =>
    Classical.choose_spec (S.exists_cl v)
  have hliftA : ∀ v ∈ C.At, lift v ∈ C.A := fun v hv =>
    ⟨(hlift v).1, by rw [(hlift v).2]; exact hv⟩
  let δ : G → ZMod 2 := fun a => chi H a + chi H' a
  have hδ : ∀ a ∈ C.A, δ (lift (S.cl a)) = δ a := fun a ha =>
    chi_eq_of_cl_eq hH hH' (hliftA _ ha.2) ha (hlift _).2
  let f : C.At →+ ZMod 2 :=
    { toFun := fun v => δ (lift v)
      map_zero' := by
        have h0 : δ (lift 0) = δ 1 := by
          rw [← hδ 1 C.A.one_mem, S.cl_one]
        change δ (lift 0) = 0
        rw [h0]
        simp [δ, chi, H.one_mem, H'.one_mem]
      map_add' := fun v w => by
        have hv := hliftA _ v.2
        have hw := hliftA _ w.2
        have hvw : S.cl (lift v * lift w) = ((v + w : C.At) : S.Qt) := by
          rw [S.cl_mul hv.1 hw.1, (hlift _).2, (hlift _).2]
          rfl
        change δ (lift ((v + w : C.At) : S.Qt)) = δ (lift v) + δ (lift w)
        rw [← hvw, hδ _ (C.A.mul_mem hv hw)]
        simp only [δ]
        rw [chi_mul hH hv hw, chi_mul hH' hv hw]
        abel }
  obtain ⟨w, hw, hwf⟩ := C.exists_mem_Bt_polar_eq f
  obtain ⟨q, hq, rfl⟩ := S.exists_cl w
  refine ⟨q, ⟨hq, hw⟩, fun h hh => ?_⟩
  have hhA := hH.1 hh
  have hval : polar S.q (S.cl h) (S.cl q) = chi H' h := by
    rw [hwf _ hhA.2]
    change δ (lift (S.cl h)) = _
    rw [hδ h hhA]
    simp [δ, chi, hh]
  rcases S.mul_comm_or hq hhA.1 with hc | hc
  · have h0 : polar S.q (S.cl h) (S.cl q) = 0 := (S.polar_cl_eq_zero_iff hhA.1 hq).mpr hc.symm
    rw [h0] at hval
    have hh' : h ∈ H' := by
      by_contra hn
      simp [chi, hn] at hval
    rw [hc, mul_inv_cancel_right]
    exact hh'
  · have hne : h * q ≠ q * h := by
      intro he
      rw [he] at hc
      exact S.z_ne_one (by simpa using hc.symm)
    have h1 : polar S.q (S.cl h) (S.cl q) = 1 := (S.polar_cl_eq_one_iff hhA.1 hq).mpr hne
    rw [h1] at hval
    have hh' : h ∉ H' := by
      intro hn
      simp [chi, hn] at hval
    rw [hc, mul_assoc, mul_inv_cancel_right, ← S.z_comm (S.QG_le_M (C.A_le_QG hhA))]
    exact (hH'.2.2 h hhA).resolve_left hh'

end Config

structure Levi (C : Config S) where
  L : Subgroup G
  H₀ : Subgroup G
  L_le_X : L ≤ C.X
  eq_one_of_mem_QG : ∀ l ∈ L, l ∈ S.QG → l = 1
  exists_mul_eq : ∀ x ∈ C.X, ∃ q ∈ S.QG, ∃ l ∈ L, q * l = x
  isZCompl : C.IsZCompl H₀
  conj_mem_H₀ : ∀ l ∈ L, ∀ h ∈ H₀, l * h * l⁻¹ ∈ H₀

namespace Config

omit [Finite G] in
theorem conj_eq_of_conj_mul_z_eq {l a : G} (hl : l ∈ S.M) (h : l * (a * S.z) * l⁻¹ = a * S.z) :
    l * a * l⁻¹ = a := by
  have hlz : l * S.z * l⁻¹ = S.z := by rw [S.z_comm hl, mul_inv_cancel_right]
  calc l * a * l⁻¹ = l * (a * S.z) * l⁻¹ * (l * S.z * l⁻¹)⁻¹ := by group
    _ = a := by rw [h, hlz, mul_inv_cancel_right]

theorem nonempty_levi (h5 : 5 ≤ S.width) : Nonempty (Levi C) := by
  obtain ⟨K, hKN, hNAK, hKA⟩ := C.exists_K h5
  obtain ⟨H₀, hH₀⟩ := C.exists_isZCompl
  refine ⟨⟨K ⊓ (S.M ⊓ normalizer (H₀ : Set G)), H₀, ?_, ?_, ?_, hH₀, ?_⟩⟩
  · intro l hl
    rw [C.X_eq]
    exact ⟨hKN hl.1, hl.2.1⟩
  · intro l hl hlQ
    have hcomm : ∀ h ∈ H₀, l * h * l⁻¹ = h := by
      intro h hh
      have hhA := hH₀.1 hh
      have h1 : l * h * l⁻¹ ∈ H₀ := (mem_normalizer_iff.mp hl.2.2 h).mp hh
      rcases S.mul_comm_or hlQ hhA.1 with hc | hc
      · rw [hc, mul_inv_cancel_right]
      · exfalso
        rw [hc, mul_assoc, mul_inv_cancel_right] at h1
        apply hH₀.2.1
        have := H₀.mul_mem h1 (H₀.inv_mem hh)
        rwa [mul_inv_cancel_right] at this
    have hcA : l ∈ centralizer (C.A : Set G) := by
      rw [mem_centralizer_iff]
      intro a ha
      have h1 : l * a * l⁻¹ = a := by
        rcases hH₀.2.2 a ha with h | h
        · exact hcomm a h
        · exact conj_eq_of_conj_mul_z_eq hl.2.1 (hcomm _ h)
      calc a * l = l * a * l⁻¹ * l := by rw [h1]
        _ = l * a := by group
    rw [show C.A = S.clPre C.At from rfl, C.centralizer_A] at hcA
    exact hKA l hl.1 hcA
  · intro x hx
    have hxM := C.X_le_M hx
    let H' : Subgroup G := H₀.comap (MulAut.conj x⁻¹).toMonoidHom
    have hmemH' : ∀ g, g ∈ H' ↔ x⁻¹ * g * x ∈ H₀ := fun g => by
      simp [H']
    have hH' : C.IsZCompl H' := by
      refine ⟨fun g hg => ?_, fun hz => ?_, fun a ha => ?_⟩
      · have := C.conj_mem_A hx (hH₀.1 ((hmemH' g).mp hg))
        rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_assoc, mul_inv_cancel,
          mul_one] at this
      · apply hH₀.2.1
        have := (hmemH' _).mp hz
        have e : x⁻¹ * S.z * x = S.z := by rw [mul_assoc, ← S.z_comm hxM, inv_mul_cancel_left]
        rwa [e] at this
      · have hxa : x⁻¹ * a * x ∈ C.A := by
          have := C.conj_mem_A (C.X.inv_mem hx) ha
          rwa [inv_inv] at this
        rcases hH₀.2.2 _ hxa with h | h
        · exact Or.inl ((hmemH' a).mpr h)
        · right
          rw [hmemH']
          have hxz : x⁻¹ * (a * S.z) * x = x⁻¹ * a * x * S.z := by
            calc x⁻¹ * (a * S.z) * x = x⁻¹ * a * (S.z * x) := by group
              _ = x⁻¹ * a * (x * S.z) := by rw [S.z_comm hxM]
              _ = x⁻¹ * a * x * S.z := by group
          rw [hxz]
          exact h
    obtain ⟨q, hqB, hq⟩ := exists_mem_B_conj hH' hH₀
    have hqx : ∀ h ∈ H₀, (q * x) * h * (q * x)⁻¹ ∈ H₀ := fun h hh => by
      have h1 : x * h * x⁻¹ ∈ H' := by
        rw [hmemH']
        simpa [mul_assoc] using hh
      have := hq _ h1
      simpa [mul_assoc] using this
    have hqxN : q * x ∈ C.N := C.X_le_normalizer (C.X.mul_mem (C.QG_le_X hqB.1) hx)
    obtain ⟨a, ha, k, hk, hak⟩ := hNAK _ hqxN
    have hk' : k = a⁻¹ * (q * x) := eq_inv_mul_of_mul_eq hak
    have haM : a ∈ S.M := S.QG_le_M (C.A_le_QG ha)
    have hqM : q ∈ S.M := S.QG_le_M hqB.1
    refine ⟨q⁻¹ * a, S.QG.mul_mem (S.QG.inv_mem hqB.1) (C.A_le_QG ha), k,
      ⟨hk, ?_, ?_⟩, ?_⟩
    · rw [hk']
      exact S.M.mul_mem (S.M.inv_mem haM) (S.M.mul_mem hqM hxM)
    · refine mem_normalizer_of_forall_conj_mem fun h hh => ?_
      have hy := hqx h hh
      have hyA := hH₀.1 hy
      have : k * h * k⁻¹ = (q * x) * h * (q * x)⁻¹ := by
        rw [hk']
        calc a⁻¹ * (q * x) * h * (a⁻¹ * (q * x))⁻¹
            = a⁻¹ * ((q * x) * h * (q * x)⁻¹ * a) := by group
          _ = a⁻¹ * (a * ((q * x) * h * (q * x)⁻¹)) := by rw [C.A_comm hyA ha]
          _ = (q * x) * h * (q * x)⁻¹ := by group
      rw [this]
      exact hy
    · rw [mul_assoc, hak, inv_mul_cancel_left]
  · intro l hl h hh
    exact (mem_normalizer_iff.mp hl.2.2 h).mp hh

end Config

end CFSG.LargeExtraspecial.GLR
