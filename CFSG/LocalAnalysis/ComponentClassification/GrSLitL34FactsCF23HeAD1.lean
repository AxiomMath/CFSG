module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23HePsi

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.CatFactsL4U4
open CFSG.ComponentClassification.CatFactsL4U4.OutInv CFSG.ComponentClassification.GrSLit.L34Facts

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] [Finite G] {X : Subgroup G} {k : G}
    (hk : ∀ y ∈ X, k * y * k⁻¹ ∈ X) : k ∈ normalizer (X : Set G) := by
  have hpow : ∀ n : ℕ, ∀ y ∈ X, k ^ n * y * (k ^ n)⁻¹ ∈ X := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
      intro y hy
      have := ih _ (hk y hy)
      rw [pow_succ]
      simpa [mul_assoc] using this
  rw [mem_normalizer_iff]
  intro y
  refine ⟨hk y, fun hy => ?_⟩
  have h1 := hpow (orderOf k - 1) _ hy
  have h2 : k ^ (orderOf k - 1) * k = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos k), pow_orderOf_eq_one]
  rw [eq_inv_of_mul_eq_one_left h2, inv_inv] at h1
  simpa [mul_assoc] using h1

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

section Ident

variable
  (hZ : center (OddBar h.K) = ⊥) {ι : ↥(NL hKa) →* Equiv.Perm (Fin 8330)}
  (hιinj : Function.Injective ι) (hιP : ∀ γ, ι γ ∈ heP) (hιsurj : ∀ p ∈ heP, ∃ γ, ι γ = p)
  (hαN : phi hKa (abar h) ∈ NL hKa) (hια : ι ⟨phi hKa (abar h), hαN⟩ = heGenPerm 0)
  (hιJ : ∀ γ : ↥(NL hKa), (γ : ↥(GAut hKa)) ∈ Jhat hKa ↔ ι γ ∈ hjJ)

include hιinj hια in
theorem comm_iff_of_ident (γ : ↥(NL hKa)) :
    γ * ⟨phi hKa (abar h), hαN⟩ = ⟨phi hKa (abar h), hαN⟩ * γ ↔
      ι γ * heGenPerm 0 = heGenPerm 0 * ι γ := by
  rw [← hια, ← map_mul, ← map_mul]
  exact ⟨fun h1 => by rw [h1], fun h1 => hιinj h1⟩

include hιinj hιP hιsurj hια in
theorem map_centralizer_ident :
    (centralizer ({⟨phi hKa (abar h), hαN⟩} : Set ↥(NL hKa))).map ι =
      centralizerIn heP (heGenPerm 0) := by
  ext g
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact mem_centralizerIn.2 ⟨hιP γ, (comm_iff_of_ident hKa hιinj hαN hια γ).1
      (mem_centralizer_singleton_iff.mp hγ)⟩
  · intro hg
    obtain ⟨hgP, hgt⟩ := mem_centralizerIn.1 hg
    obtain ⟨γ, rfl⟩ := hιsurj g hgP
    exact ⟨γ, mem_centralizer_singleton_iff.mpr
      ((comm_iff_of_ident hKa hιinj hαN hια γ).2 hgt), rfl⟩

include hZ hιinj hιP hια hιJ in
theorem mem_normalizer_of_comm {k : ↥h.K}
    (hk : piK hKa k * ⟨phi hKa (abar h), hαN⟩ = ⟨phi hKa (abar h), hαN⟩ * piK hKa k) :
    (k : H) ∈ normalizer ((GSLit.fixedLayer h.J h.B ⊔ oddCoreIn h.W : Subgroup H) : Set H) := by
  have hkC : ι (piK hKa k) ∈ centralizerIn heP (heGenPerm 0) :=
    mem_centralizerIn.2 ⟨hιP _, (comm_iff_of_ident hKa hιinj hαN hια _).1 hk⟩
  have hnorm := Subgroup.normal_of_index_eq_two index_hjJ
  have hkW : (k : H) ∈ h.W := K_le_W h k.2
  apply mem_normalizer_of_conj_mem
  intro y hy
  have hsup : (GSLit.fixedLayer h.J h.B ⊔ oddCoreIn h.W).map (MulAut.conj (k : H)).toMonoidHom ≤
      GSLit.fixedLayer h.J h.B ⊔ oddCoreIn h.W := by
    rw [Subgroup.map_sup, sup_le_iff]
    constructor
    · rintro _ ⟨j, hj, rfl⟩
      have hjK : j ∈ h.K := fixedLayer_le_K h hKa hj
      set j' : ↥h.K := ⟨(k : H) * j * (k : H)⁻¹, mul_mem (mul_mem k.2 hjK) (inv_mem k.2)⟩ with hj'
      have hj'eq : piK hKa j' = piK hKa k * piK hKa ⟨j, hjK⟩ * (piK hKa k)⁻¹ := by
        rw [← map_mul, ← map_inv, ← map_mul]
        congr 1
      have hιj : ι (piK hKa ⟨j, hjK⟩) ∈ hjJ := (hιJ _).1 (piK_mem_Jhat hKa hj)
      have hιj' : ι (piK hKa j') ∈ hjJ := by
        rw [hj'eq, map_mul, map_mul, map_inv]
        have h1 : (⟨ι (piK hKa k), hkC⟩ : ↥(centralizerIn heP (heGenPerm 0))) *
            ⟨ι (piK hKa ⟨j, hjK⟩), hjJ_le hιj⟩ * (⟨ι (piK hKa k), hkC⟩)⁻¹ ∈
              hjJ.subgroupOf (centralizerIn heP (heGenPerm 0)) :=
          hnorm.conj_mem _ (mem_subgroupOf.mpr hιj) _
        rw [mem_subgroupOf] at h1
        simpa using h1
      obtain ⟨j₀, hj₀B, hj₀⟩ := exists_piK_of_mem_Jhat hKa ((hιJ _).2 hιj')
      have hodd : j₀⁻¹ * j' ∈ pPrimeCore 2 ↥h.K := by
        rw [← piK_eq_one_iff hKa hZ, map_mul, map_inv, hj₀, inv_mul_cancel]
      have hoW := mem_pPrimeCore_W_of_mem_pPrimeCore hKa hodd
      have hsplit : (k : H) * j * (k : H)⁻¹ = (j₀ : H) * ((j₀⁻¹ * j' : ↥h.K) : H) := by
        simp [hj']
      show (MulAut.conj (k : H)) j ∈ _
      rw [MulAut.conj_apply, hsplit]
      exact mul_mem (mem_sup_left hj₀B) (mem_sup_right ⟨_, hoW, rfl⟩)
    · rintro _ ⟨o, ⟨o', ho', rfl⟩, rfl⟩
      have hc : (⟨(k : H), hkW⟩ : ↥h.W) * o' * (⟨(k : H), hkW⟩ : ↥h.W)⁻¹ ∈ pPrimeCore 2 ↥h.W :=
        (pPrimeCore_normal (p := 2) (G := ↥h.W)).conj_mem o' ho' _
      refine mem_sup_right ⟨_, hc, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      simp
  have := hsup ⟨y, hy, rfl⟩
  simpa [MulAut.conj_apply] using this

end Ident

end CFSG.ComponentClassification.GSThmB.CF23L34
