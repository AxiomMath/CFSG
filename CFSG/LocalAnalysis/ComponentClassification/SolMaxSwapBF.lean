module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapBB

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace SwapP2

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {M : Subgroup X} {e₀ : X} {F : Subgroup X} {DF : Finset (Fin n)} {r : X}

theorem exists_side_involution (hs : Setting t J n e E D M) (hn : 9 ≤ n)
    (hd : Data t J n e E D M e₀ F DF r) (he₀H : centralizer ({e₀} : Set X) ≤ Hn E)
    {N₁ : Subgroup X} (hN₁C : N₁ ≤ centralizer ({r} : Set X))
    (hN₁pc : IsPComponent 2 (N₁.subgroupOf (centralizer ({r} : Set X))))
    (hK : ∀ B : Subgroup X, B ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X) →
      IsPComponent 2 (B.subgroupOf (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))) →
      (∀ x ∈ B, ∀ z ∈ fixA M e₀ r,
        x * z * x⁻¹ * z⁻¹ ∈ (pPrimeCore 2 ↥(fixA M e₀ r)).map (fixA M e₀ r).subtype) →
      B ≤ UnbalancedLayer.coreActionKernel N₁ ∧
        B ≤ UnbalancedLayer.coreActionKernel (conjBy N₁ e₀)) :
    ∀ f ∈ F, ∃ a ∈ fixA M e₀ r, a * a = 1 ∧
      f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel (N₁ ⊔ conjBy N₁ e₀) ∧
        f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel M := by
  intro f hf
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S := hs.sig
  have hn9 := S.nine_le
  obtain ⟨θ⟩ := hs.alt
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
  have htH : t ∈ Hn E := hs.cent (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hs.le hs.pc htH
  have hMtt : conjBy (conjBy M t) t = M := conjBy_conjBy_of_mul_self M ht2
  have hneT : (conjBy M t).map (MulAut.conj t).toMonoidHom ≠ conjBy M t := by
    change conjBy (conjBy M t) t ≠ conjBy M t
    rw [hMtt]
    exact Ne.symm hs.swap
  have hJMt : J ≤ conjBy M t ⊔ (conjBy M t).map (MulAut.conj t).toMonoidHom := by
    change J ≤ conjBy M t ⊔ conjBy (conjBy M t) t
    rw [hMtt, sup_comm]
    exact hs.diag
  let θt : ↥(conjBy M t) ⧸ pPrimeCore 2 ↥(conjBy M t) ≃* alternatingGroup (Fin n) :=
    (Sol78.coreQuotCongr (M.equivMapOfInjective (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective)).symm.trans θ
  obtain ⟨ρt, hρt⟩ := exists_isPermAction (M := conjBy M t) (by omega) (by omega) θt
  have hJN : J ≤ normalizer (M : Set X) := le_normalizer_of_swap htH hs.le hs.pc hs.swap hs.diag
  have hJNt : J ≤ normalizer (conjBy M t : Set X) :=
    le_normalizer_of_swap htH hMtH hMtpc hneT hJMt
  obtain ⟨π, hπ⟩ := S.exists_perm_compat_of_swap hs.cent hs.le hs.pc hs.swap hs.diag hρ
  obtain ⟨πt, hπt⟩ := S.exists_perm_compat_of_swap hs.cent hMtH hMtpc hneT hJMt hρt
  have hMtK : conjBy M t ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hs.le hMtH hs.pc hMtpc (Ne.symm hs.swap)
  have hMKt : M ≤ UnbalancedLayer.coreActionKernel (conjBy M t) :=
    GSThmB.B5a.le_coreActionKernel_of_ne hMtH hs.le hMtpc hs.pc hs.swap
  have he₀J : e₀ ∈ J := S.le hd.e₀E
  have he₀N := hJN he₀J
  have he₀Nt := hJNt he₀J
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ hd.e₀E
  have he₀r : e₀ ∈ centralizer ({r} : Set X) := mem_centralizer_singleton_iff.mpr hd.re₀.symm
  have hfJ : f ∈ J := hd.FJ hf
  have hfN := hJN hfJ
  have hfNt := hJNt hfJ
  have hf2 : f * f = 1 := by rw [← sq]; exact (card_sq_of_klein hd.Fk).2 f hf
  have hrK : r ∈ UnbalancedLayer.coreActionKernel M := hMtK hd.rM
  have hrNt : r ∈ normalizer (conjBy M t : Set X) := le_normalizer hd.rM
  have he₀4 : (ρ ⟨e₀, he₀N⟩).support.card = 4 := by
    rw [hπ e₀ he₀J he₀N, Perm.card_support_conj]
    exact S.card_support_coreImage_E hd.e₀E hd.e₀1
  have he₀4t : (ρt ⟨e₀, he₀Nt⟩).support.card = 4 := by
    rw [hπt e₀ he₀J he₀Nt, Perm.card_support_conj]
    exact S.card_support_coreImage_E hd.e₀E hd.e₀1
  set U := zpowers e₀ ⊔ zpowers r ⊔ zpowers f with hUdef
  have he₀f : e₀ ∈ centralizer ({f} : Set X) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hd.Fe₀ hf)).symm
  have hrf : r ∈ centralizer ({f} : Set X) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hd.rF hf)).symm
  have hU2 : IsPGroup 2 ↥U := by
    refine IsPGroup.to_sup_of_normal_right' (IsPGroup.to_sup_of_normal_right'
      (isPGroup_zpowers_of_mul_self he₀2) (isPGroup_zpowers_of_mul_self hd.r2) ?_)
      (isPGroup_zpowers_of_mul_self hf2) ?_
    · rw [zpowers_le]
      refine centralizer_le_normalizer _ ?_
      rw [centralizer_zpowers_eq' r]
      exact mem_centralizer_singleton_iff.mpr hd.re₀.symm
    · refine sup_le ?_ ?_ <;> rw [zpowers_le] <;> refine centralizer_le_normalizer _ ?_ <;>
        rw [centralizer_zpowers_eq' f]
      · exact he₀f
      · exact hrf
  have hUM : U ≤ normalizer (M : Set X) :=
    sup_le (sup_le (zpowers_le.mpr he₀N) (zpowers_le.mpr hrK.1)) (zpowers_le.mpr hfN)
  have hUMt : U ≤ normalizer (conjBy M t : Set X) :=
    sup_le (sup_le (zpowers_le.mpr he₀Nt) (zpowers_le.mpr hrNt)) (zpowers_le.mpr hfNt)
  have hUf : U ≤ centralizer ({f} : Set X) :=
    sup_le (sup_le (zpowers_le.mpr he₀f) (zpowers_le.mpr hrf))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
  have hV : Odd (Nat.card ↥(M ⊓ conjBy M t)) := by
    have hle : M ⊓ conjBy M t ≤ (pPrimeCore 2 ↥M).map M.subtype := fun z hz =>
      mem_core_of_mem_coreActionKernel hρ (by omega) (mem_inf.mp hz).1 (hMtK (mem_inf.mp hz).2)
    have h1 : Odd (Nat.card ↥((pPrimeCore 2 ↥M).map M.subtype)) := by
      rw [card_map_of_injective M.subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact h1.of_dvd_nat (card_dvd_of_le hle)
  obtain ⟨a, haM, b, hbMt, hfab, ha2, hb2, hab, hUa, hUb⟩ :=
    exists_involution_decomp (fun z hz => (hMKt hz).1) hV hU2 hUM hUMt (hs.diag hfJ) hf2
      (mem_sup_right (mem_zpowers f)) hUf
  have hae₀ : a * e₀ = e₀ * a :=
    (mem_centralizer_singleton_iff.mp (hUa (mem_sup_left (mem_sup_left (mem_zpowers e₀))))).symm
  have har : a * r = r * a :=
    (mem_centralizer_singleton_iff.mp (hUa (mem_sup_left (mem_sup_right (mem_zpowers r))))).symm
  have hbe₀ : b * e₀ = e₀ * b :=
    (mem_centralizer_singleton_iff.mp (hUb (mem_sup_left (mem_sup_left (mem_zpowers e₀))))).symm
  have hbr : b * r = r * b :=
    (mem_centralizer_singleton_iff.mp (hUb (mem_sup_left (mem_sup_right (mem_zpowers r))))).symm
  have hρa : coreImage θ haM = ρ ⟨f, hfN⟩ := by
    have h1 := hρ.eq_one_of_mem_coreActionKernel (by omega) (hMtK hbMt)
    have h2 : (⟨f, hfN⟩ : ↥(normalizer (M : Set X))) =
        ⟨a, le_normalizer haM⟩ * ⟨b, (hMtK hbMt).1⟩ := Subtype.ext hfab
    rw [h2, map_mul, h1, mul_one]
    exact (hρ.apply_of_mem (by omega) ⟨a, haM⟩).symm
  have hρb : coreImage θt hbMt = ρt ⟨f, hfNt⟩ := by
    have h1 := hρt.eq_one_of_mem_coreActionKernel (by omega) (hMKt haM)
    have h2 : (⟨f, hfNt⟩ : ↥(normalizer (conjBy M t : Set X))) =
        ⟨a, (hMKt haM).1⟩ * ⟨b, le_normalizer hbMt⟩ := Subtype.ext hfab
    rw [h2, map_mul, h1, one_mul]
    exact (hρt.apply_of_mem (by omega) ⟨b, hbMt⟩).symm
  have hFs : ∀ ω ∉ DF, coreImage e hfJ ω = ω := fun ω hω => hd.Fs ⟨f, hfJ⟩ hf ω hω
  have hEs : ∀ ω ∉ D, coreImage e he₀J ω = ω := fun ω hω => S.supp ⟨e₀, he₀J⟩ hd.e₀E ω hω
  obtain ⟨-, -, -, hmemA⟩ := fixedLayer_fixedLayer_facts hs.le hs.pc hρ he₀N he₀2 he₀4.le
    (by omega) he₀H hd.re₀ hd.r2 hd.r1 hrK.1 (Or.inl hrK)
  have haA : a ∈ fixA M e₀ r := by
    refine hmemA a haM hae₀ har ha2 ?_
    rw [hρa, hπ f hfJ hfN, hπ e₀ he₀J he₀N]
    exact support_conj_subset_compl_of_disjoint π _ _ hFs hEs hd.disj
  obtain ⟨hBle, hBpc, hBMt, hmemB⟩ := fixedLayer_fixedLayer_facts hMtH hMtpc hρt he₀Nt he₀2
    he₀4t.le (by omega) he₀H hd.re₀ hd.r2 hd.r1 hrNt (Or.inr hd.lift)
  have hbB : b ∈ fixB M t e₀ r := by
    refine hmemB b hbMt hbe₀ hbr hb2 ?_
    rw [hρb, hπt f hfJ hfNt, hπt e₀ he₀J he₀Nt]
    exact support_conj_subset_compl_of_disjoint πt _ _ hFs hEs hd.disj
  have hArM : fixA M e₀ r ≤ M :=
    ((GSLit.fixedLayer_le_inf _ (zpowers r)).trans inf_le_left).trans
      ((GSLit.fixedLayer_le_inf M (zpowers e₀)).trans inf_le_left)
  have hBA : ∀ x ∈ fixB M t e₀ r, ∀ z ∈ fixA M e₀ r,
      x * z * x⁻¹ * z⁻¹ ∈ (pPrimeCore 2 ↥(fixA M e₀ r)).map (fixA M e₀ r).subtype := by
    intro x hx z hz
    have hxM : x ∈ UnbalancedLayer.coreActionKernel M := hMtK (hBMt hx)
    have hxe₀ : x ∈ centralizer ({e₀} : Set X) := (hBle hx).2
    have hxr : x ∈ centralizer ({r} : Set X) := (hBle hx).1
    have hxA : x ∈ normalizer (GSLit.fixedLayer M (zpowers e₀) : Set X) := by
      refine GSLit.mem_normalizer_fixedLayer hxM.1 (centralizer_le_normalizer _ ?_)
      rw [centralizer_zpowers_eq' e₀]
      exact hxe₀
    have hxAr : x ∈ normalizer (fixA M e₀ r : Set X) := by
      refine GSLit.mem_normalizer_fixedLayer hxA (centralizer_le_normalizer _ ?_)
      rw [centralizer_zpowers_eq' r]
      exact hxr
    have h1 : x * z * x⁻¹ * z⁻¹ ∈ fixA M e₀ r :=
      mul_mem ((mem_normalizer_iff.mp hxAr z).mp hz) (inv_mem hz)
    have h2 : x * z * x⁻¹ * z⁻¹ ∈ (pPrimeCore 2 ↥M).map M.subtype := by
      have h3 := (UnbalancedLayer.mem_coreActionKernel.mp (inv_mem hxM)).2 z (hArM hz)
      rw [inv_inv] at h3
      have h4 := (mem_normalizer_iff.mp (le_normalizer_pPrimeCore (le_normalizer (hArM hz)))
        _).mp h3
      rwa [show z * (z⁻¹ * x * z * x⁻¹) * z⁻¹ = x * z * x⁻¹ * z⁻¹ by group] at h4
    exact inf_pPrimeCore_le hArM ⟨h1, h2⟩
  obtain ⟨hN₁xC, hN₁xpc⟩ := isPComponent_conj hN₁C hN₁pc he₀r
  obtain ⟨hK₁, hK₂⟩ := hK _ hBle hBpc hBA
  have hb₁ : b ∈ UnbalancedLayer.coreActionKernel N₁ := hK₁ hbB
  have hb₂ : b ∈ UnbalancedLayer.coreActionKernel (conjBy N₁ e₀) := hK₂ hbB
  have hnorm : N₁ ≤ normalizer (conjBy N₁ e₀ : Set X) ∧
      conjBy N₁ e₀ ≤ normalizer (N₁ : Set X) := by
    by_cases h : conjBy N₁ e₀ = N₁
    · rw [h]
      exact ⟨le_normalizer, le_normalizer⟩
    · exact ⟨fun z hz => (GSThmB.B5a.le_coreActionKernel_of_ne hN₁xC hN₁C hN₁xpc hN₁pc h hz).1,
        fun z hz => (GSThmB.B5a.le_coreActionKernel_of_ne hN₁C hN₁xC hN₁pc hN₁xpc (Ne.symm h)
          hz).1⟩
  have hfa : f * a⁻¹ = b := by
    rw [hfab, hab, mul_inv_cancel_right]
  refine ⟨a, haA, ha2, ?_, ?_⟩
  · rw [hfa]
    exact mem_coreActionKernel_sup hnorm.1 hnorm.2 hb₁ hb₂
  · rw [hfa]
    exact hMtK hbMt

theorem pumpSide_of_commute (hs : Setting t J n e E D M) (hn : 9 ≤ n)
    (hd : Data t J n e E D M e₀ F DF r) (he₀H : centralizer ({e₀} : Set X) ≤ Hn E)
    {N₁ : Subgroup X} (hN₁C : N₁ ≤ centralizer ({r} : Set X))
    (hN₁pc : IsPComponent 2 (N₁.subgroupOf (centralizer ({r} : Set X))))
    (hK : ∀ B : Subgroup X, B ≤ centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X) →
      IsPComponent 2 (B.subgroupOf (centralizer ({r} : Set X) ⊓ centralizer ({e₀} : Set X))) →
      (∀ x ∈ B, ∀ z ∈ fixA M e₀ r,
        x * z * x⁻¹ * z⁻¹ ∈ (pPrimeCore 2 ↥(fixA M e₀ r)).map (fixA M e₀ r).subtype) →
      B ≤ UnbalancedLayer.coreActionKernel N₁ ∧
        B ≤ UnbalancedLayer.coreActionKernel (conjBy N₁ e₀)) :
    ∀ f ∈ F, ∃ a ∈ fixA M e₀ r,
      f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel (N₁ ⊔ conjBy N₁ e₀) ∧
        f * a⁻¹ ∈ UnbalancedLayer.coreActionKernel M := by
  intro f hf
  obtain ⟨a, ha, -, h1, h2⟩ := exists_side_involution hs hn hd he₀H hN₁C hN₁pc hK f hf
  exact ⟨a, ha, h1, h2⟩

end SwapP2

end CFSG.ComponentClassification.SolMax
