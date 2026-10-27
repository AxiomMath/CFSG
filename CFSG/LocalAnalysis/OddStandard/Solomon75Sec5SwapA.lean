module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapNorm

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

section Basic

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))} {s : X}

theorem Z_le_centralizer_of_frac53 (hF : Solomon75Frac53) (h : Sec5Data X n z Z S)
    (hs : IsSec5Inv X Z s) : Z ≤ centralizer ({s} : Set X) := by
  classical
  refine h.pair.le_closure_witnessSet.trans ((Subgroup.closure_le _).2 ?_)
  rintro u ⟨huZ, L, hL, hLn⟩
  obtain ⟨h1, h2, -⟩ := h.pair.isIntrinsicIn_normalizer huZ hL hLn
  set E : Subgroup X := oTwoPrimeOf (L ⊓ centralizer (Z : Set X)) with hE
  have hEc : Sec5Comp X n (normalizer (Z : Set X)) E := ⟨⟨u, h1⟩, h2⟩
  have huE : u ∈ E := h1.2.1
  have hu1 : u ≠ 1 := by
    intro hu
    have := h1.1
    rw [hu, orderOf_one] at this
    omega
  refine Subgroup.mem_centralizer_singleton_iff.2 ?_
  by_cases hsE : s ∈ normalizer (E : Set X)
  · exact comm_of_mem_Z_of_norm h hs hEc hsE huZ huE hu1
  set E' : Subgroup X := E.map (MulAut.conj s).toMonoidHom with hE'
  have hE'c : Sec5Comp X n (normalizer (Z : Set X)) E' :=
    hEc.map_conj (Subgroup.le_normalizer hs.mem)
  have hne : E ≠ E' := fun heq => hsE (mem_normalizer_of_map_conj_eq heq.symm)
  have hzs := (hF X n z Z S h s hs).2 E E' hEc hE'c hne rfl
  set D : Subgroup X := K0 X n (normalizer (Z : Set X)) with hD
  have hEK : E ≤ D := le_sSup hEc
  have hE'K : E' ≤ D := le_sSup hE'c
  have hZD : Z ≤ D := h.Z_le_K0
  have hodd : Odd (Nat.card (oddCoreOf D)) := odd_card_oddCoreOf D
  have hZ1 : ∀ x ∈ Z, x ∈ oddCoreOf D → x = 1 := fun x hx hxO =>
    eq_one_of_mem_of_mem_odd (oddCoreOf D) Z hodd h.isPGroup_Z hx hxO
  have huzE : u ∈ zStar E := mem_zStar_of_mem_of_le_centralizer huE fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.2 (h.Z_le_center_K0 huZ (hEK hk)).symm
  have hu' : u ∈ zStar E' ⊔ oddCoreOf D := hzs ▸ Subgroup.mem_sup_left huzE
  set u' : X := s * u * s⁻¹ with hu'def
  have hu'Z : u' ∈ Z := (Subgroup.mem_normalizer_iff.1 hs.mem u).1 huZ
  have hu'E' : u' ∈ E' := ⟨u, huE, rfl⟩
  have hu'1 : u' ≠ 1 := by
    intro h1'
    apply hu1
    have := congrArg (fun t => s⁻¹ * t * s) h1'
    simpa [hu'def, mul_assoc] using this
  have hu'zE' : u' ∈ zStar E' := mem_zStar_of_mem_of_le_centralizer hu'E' fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.2 (h.Z_le_center_K0 hu'Z (hE'K hk)).symm
  obtain ⟨⟨w', hw'⟩, hE'n⟩ := hE'c
  have hzw : zStar E' ≤ pPrimeCoreOf 2 E' ⊔ Subgroup.zpowers w' := hw'.zStar_le_sup_zpowers hE'n
  have hOE' : pPrimeCoreOf 2 E' ≤ oddCoreOf D :=
    oddCoreOf_le_of_isPCompIn ⟨hE'K, isPComponent_subgroupOf_mono hE'K (K0_le n _) hw'.2.2.1.2⟩
  have hw'D : w' ∈ D := hE'K hw'.2.1
  have hP : ∀ x ∈ zStar E', x ∈ oddCoreOf D ⊔ Subgroup.zpowers w' := fun x hx =>
    (sup_le_sup_right hOE' _) (hzw hx)
  have hnormD : Subgroup.zpowers w' ≤ normalizer (oddCoreOf D : Set X) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_pPrimeCoreOf_of_mem hw'D
  have hform : ∀ x ∈ Z, x ≠ 1 → x ∈ oddCoreOf D ⊔ Subgroup.zpowers w' →
      ∃ o ∈ oddCoreOf D, x = o * w' := by
    intro x hxZ hx1 hxP
    obtain ⟨o, ho, t, ht, rfl⟩ :=
      (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing (oddCoreOf D) (Subgroup.zpowers w')
        hnormD x).1 hxP
    rcases zpowers_eq_of_orderOf_two hw'.1 t ht with h1 | h1
    · exfalso
      rw [h1, mul_one] at hxZ hx1
      exact hx1 (hZ1 o hxZ ho)
    · exact ⟨o, ho, by rw [h1]⟩
  have hu_in : u ∈ oddCoreOf D ⊔ Subgroup.zpowers w' := by
    have hle : zStar E' ⊔ oddCoreOf D ≤ oddCoreOf D ⊔ Subgroup.zpowers w' :=
      sup_le (fun x hx => hP x hx) le_sup_left
    exact hle hu'
  obtain ⟨o₁, ho₁, hu_eq⟩ := hform u huZ hu1 hu_in
  obtain ⟨o₂, ho₂, hu'_eq⟩ := hform u' hu'Z hu'1 (hP u' hu'zE')
  have hdiff : u * u'⁻¹ ∈ oddCoreOf D := by
    have : u * u'⁻¹ = o₁ * o₂⁻¹ := by
      rw [hu_eq, hu'_eq]; group
    rw [this]
    exact (oddCoreOf D).mul_mem ho₁ ((oddCoreOf D).inv_mem ho₂)
  have hu_eq' : u * u'⁻¹ = 1 :=
    hZ1 _ (Z.mul_mem huZ (Z.inv_mem hu'Z)) hdiff
  have : u' = u := by
    have := mul_inv_eq_one.1 hu_eq'
    exact this.symm
  have hsu : s * u * s⁻¹ = u := by rw [← hu'def]; exact this
  have : s * u = u * s := by
    have := congrArg (fun t => t * s) hsu
    simpa [mul_assoc] using this
  exact this.symm

theorem exists_swapped_comp (h : Sec5Data X n z Z S) (hs : IsSec5Inv X Z s)
    {A : Subgroup X} (hA : Sec5Comp X n (normalizer (Z : Set X)) A)
    (hAs : A.map (MulAut.conj s).toMonoidHom ≠ A) :
    ∃ M E : Subgroup X, Sec5Comp X n (centralizer ({z} : Set X)) M ∧
      M.map (MulAut.conj s).toMonoidHom ≠ M ∧ E ≤ A ∧ E ≤ M ∧
      IsDoubleCoverOfAlt (↥E ⧸ pPrimeCore 2 ↥E) n ∧ E.subgroupOf M ⊔ pPrimeCore 2 ↥M = ⊤ := by
  classical
  have hn : 8 ≤ n := h.maxdeg.1
  have hz2 : orderOf z = 2 := h.orderOf_z
  set N : Subgroup X := normalizer (Z : Set X) with hN
  have hAK : A ≤ K0 X n N := le_sSup hA
  have hAz : A ≤ centralizer ({z} : Set X) :=
    (h.K0_le_centralizer_Z.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 h.z_mem)))
      |> fun hh => hAK.trans hh
  have hAH : A ≤ N ⊓ centralizer ({z} : Set X) := le_inf hA.isPCompIn.1 hAz
  obtain ⟨⟨u₀, hu₀⟩, hAn⟩ := id hA
  have hu₀H : IsIntrinsicIn X (N ⊓ centralizer ({z} : Set X)) A u₀ :=
    ⟨hu₀.1, hu₀.2.1, ⟨hAH, isPComponent_subgroupOf_mono hAH inf_le_left hu₀.2.2.1.2⟩,
      hu₀.2.2.2⟩
  obtain ⟨M, hM, hMn, hEM⟩ := exists_isIntrinsicIn_centralizer h.hypA h.maxdeg (s := z) hz2
    (inf_le_right : N ⊓ centralizer ({z} : Set X) ≤ centralizer ({z} : Set X)) hu₀H hAn
  have hMc : Sec5Comp X n (centralizer ({z} : Set X)) M := ⟨⟨u₀, hM⟩, hMn⟩
  set E₁ : Subgroup X := oTwoPrimeOf (A ⊓ centralizer ({u₀} : Set X)) with hE₁
  obtain ⟨hE₁A, hcovA, hE₁q⟩ := hu₀.cover_oTwoPrimeOf
  have hE₁n : IsDoubleCoverOfAlt (↥E₁ ⧸ pPrimeCore 2 ↥E₁) n :=
    (isDoubleCoverOfAlt_quot_iff_of_covers hE₁A hcovA n).2 hAn
  have hcard : Nat.card (↥M ⧸ pPrimeCore 2 ↥M) = n.factorial :=
    natCard_eq_factorial_of_isDoubleCoverOfAlt (by omega) hMn
  have hcov₁ : E₁.subgroupOf M ⊔ pPrimeCore 2 ↥M = ⊤ :=
    covers_of_card_le hEM (by
      rw [hcard, natCard_eq_factorial_of_isDoubleCoverOfAlt (by omega) hE₁n])
  refine ⟨M, E₁, hMc, fun hMs => ?_, hE₁A, hEM, hE₁n, hcov₁⟩
  set E₂ : Subgroup X := E₁.map (MulAut.conj s).toMonoidHom with hE₂
  have hE₂n : IsDoubleCoverOfAlt (↥E₂ ⧸ pPrimeCore 2 ↥E₂) n := by
    let ψ : ↥E₁ ≃* ↥E₂ := Subgroup.equivMapOfInjective E₁ _ (MulAut.conj s).injective
    obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv ψ
    exact isDoubleCoverOfAlt_congr' f hE₁n
  have hE₂M : E₂ ≤ M := by
    rw [← hMs]
    exact Subgroup.map_mono hEM
  have hcov₂ : E₂.subgroupOf M ⊔ pPrimeCore 2 ↥M = ⊤ :=
    covers_of_card_le hE₂M (by
      rw [hcard, natCard_eq_factorial_of_isDoubleCoverOfAlt (by omega) hE₂n])
  have hq : Group.IsPerfect (↥M ⧸ pPrimeCore 2 ↥M) := hMn.1.1
  set φ : ↥M →* ↥M ⧸ pPrimeCore 2 ↥M := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hφ
  have hlift : ∀ (q : ↥M ⧸ pPrimeCore 2 ↥M) (F : Subgroup X),
      F.subgroupOf M ⊔ pPrimeCore 2 ↥M = ⊤ → ∃ f : ↥M, (f : X) ∈ F ∧ φ f = q := by
    intro q F hF
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    have hm : m ∈ F.subgroupOf M ⊔ pPrimeCore 2 ↥M := hF ▸ Subgroup.mem_top m
    obtain ⟨f, hf, o, ho, hfo⟩ := Subgroup.mem_sup_of_normal_right.1 hm
    refine ⟨f, hf, ?_⟩
    rw [← hfo, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o).2 ho, mul_one]
    rfl
  set P : Subgroup ↥M := (M ⊓ oddCoreOf N).subgroupOf M with hP
  have hne : A ≠ A.map (MulAut.conj s).toMonoidHom := fun e => hAs e.symm
  have hA₂ : Sec5Comp X n N (A.map (MulAut.conj s).toMonoidHom) :=
    hA.map_conj (Subgroup.le_normalizer hs.mem)
  have hcomm : ∀ f₁ f₂ : ↥M, (f₁ : X) ∈ E₁ → (f₂ : X) ∈ E₂ → ⁅f₁, f₂⁆ ∈ P := by
    intro f₁ f₂ h₁ h₂
    have h2A : (f₂ : X) ∈ A.map (MulAut.conj s).toMonoidHom :=
      Subgroup.map_mono hE₁A h₂
    have h1 := commutator_mem_oddCoreOf_of_ne hA.isPCompIn hA₂.isPCompIn hne (hE₁A h₁) h2A
    refine Subgroup.mem_subgroupOf.2 ⟨?_, h1⟩
    exact (⁅f₁, f₂⁆ : ↥M).2
  have hPbar : (⊤ : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)) ≤ P.map φ := by
    calc (⊤ : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)) = commutator (↥M ⧸ pPrimeCore 2 ↥M) :=
          hq.commutator_eq_top.symm
      _ ≤ P.map φ := by
        rw [_root_.commutator_def, Subgroup.commutator_le]
        intro q₁ _ q₂ _
        obtain ⟨f₁, hf₁, rfl⟩ := hlift q₁ E₁ hcov₁
        obtain ⟨f₂, hf₂, rfl⟩ := hlift q₂ E₂ hcov₂
        rw [← map_commutatorElement]
        exact Subgroup.mem_map_of_mem φ (hcomm f₁ f₂ hf₁ hf₂)
  have hPtop : P.map φ = ⊤ := top_le_iff.1 hPbar
  have hdvd1 : Nat.card (↥M ⧸ pPrimeCore 2 ↥M) ∣ Nat.card P := by
    have h1 : Nat.card (P.map φ) ∣ Nat.card P := Subgroup.card_map_dvd P φ
    rwa [hPtop, Subgroup.card_top] at h1
  have hdvd2 : Nat.card P ∣ Nat.card (oddCoreOf N) := by
    refine Subgroup.card_dvd_of_injective
      (⟨⟨fun p => ⟨((p : ↥M) : X), (Subgroup.mem_subgroupOf.1 p.2).2⟩, rfl⟩, fun _ _ => rfl⟩ :
        P →* ↥(oddCoreOf N)) ?_
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun t : ↥(oddCoreOf N) => (t : X)) hab))
  have hodd : Odd (Nat.card (↥M ⧸ pPrimeCore 2 ↥M)) :=
    Odd.of_dvd_nat (Odd.of_dvd_nat (odd_card_oddCoreOf N) hdvd2) hdvd1
  have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  rw [hcard] at hodd
  have := Nat.odd_iff.1 hodd
  omega


end Basic

end CFSG.OddStandard.Solomon75
