module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eOrd
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eSp6
public import CFSG.LieType.Steinberg.CentralExt.SpThree

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51e

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

theorem NoSpin7.of_quotient {L : Type} [Group L] [Finite L] [Group.IsPerfect L] {p : ℕ}
    (N : Subgroup L) [N.Normal] (hN : N ≤ center L) (hodd : ¬ 2 ∣ Nat.card N)
    (h : NoSpin7 p (L ⧸ N)) : NoSpin7 p L := by
  intro r hr hZ hLM
  have hcard := card_center_eq N hN
  have hv : (Nat.card (center (L ⧸ N))).factorization 2 = 1 := by
    rw [hcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hodd, add_zero] at hZ
    exact hZ
  exact h r hr hv (LieType.CurtisTits.lieModel_of_mulEquiv (quotientCenterEquiv N hN).symm hLM)

theorem not_two_dvd_card_oddPart {L : Type} [Group L] [Finite L] :
    ¬ 2 ∣ Nat.card (LieType.Steinberg.oddPart (center L) le_rfl) := by
  intro h2
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have h1 := (LieType.Steinberg.mem_oddPart.1 c.2).2
  rw [Subgroup.orderOf_coe, hc] at h1
  exact (Nat.not_even_iff_odd.2 h1) even_two

theorem exists_mulEquiv_statedSp {L : Type} [Group L] [Finite L] [Group.IsPerfect L] {p f : ℕ}
    (hp2 : p ≠ 2) (hL : Blueprint.LieModel (L ⧸ center L) .PSp 3 p f)
    (hZ : (Nat.card (center L)).factorization 2 = 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧ p.Prime ∧
      Nonempty (L ⧸ LieType.Steinberg.oddPart (center L) le_rfl ≃* StatedSp 3 F) := by
  rcases hL with ⟨-, ⟨hp, -, -⟩, F, _, _, hF, ⟨e⟩⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  rotate_left
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  have hodd : Odd (Nat.card F) := hF ▸ (hp.odd_of_ne_two hp2).pow
  set N := LieType.Steinberg.oddPart (center L) le_rfl
  set η : L →* StatedProj (StatedSp 3 F) := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
    with hη
  have hηs : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : η.ker = center L := by
    ext y
    rw [MonoidHom.mem_ker, hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hNle : N ≤ η.ker := fun c hc => by
    rw [hηker]
    exact hc.1
  set η' : L ⧸ N →* StatedProj (StatedSp 3 F) := QuotientGroup.lift N η hNle
  have hη's : Function.Surjective η' := by
    intro y
    obtain ⟨x, rfl⟩ := hηs y
    exact ⟨x, rfl⟩
  have hker' : η'.ker = η.ker.map (QuotientGroup.mk' N) := QuotientGroup.ker_lift N η hNle
  have hcen' : η'.ker ≤ center (L ⧸ N) := by
    rw [hker']
    rintro _ ⟨c, hc, rfl⟩
    rw [hηker] at hc
    rw [mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    exact congrArg (QuotientGroup.mk (s := N)) (mem_center_iff.1 hc g)
  have h2' : IsPGroup 2 η'.ker := by
    rintro ⟨x, hx⟩
    rw [hker'] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    rw [hηker] at hc
    obtain ⟨a, ha⟩ := LieType.Steinberg.exists_pow_two_pow_mem_oddPart
      (le_rfl : center L ≤ center L) hc
    refine ⟨a, Subtype.ext ?_⟩
    change (QuotientGroup.mk' N c) ^ 2 ^ a = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ha
  set β : StatedSp 3 F →* StatedProj (StatedSp 3 F) := QuotientGroup.mk' _ with hβ
  have hβs : Function.Surjective β := QuotientGroup.mk'_surjective _
  have hβcard : Nat.card β.ker = 2 := by
    rw [hβ, QuotientGroup.ker_mk', ← LieType.Universal.Symplectic.center_eq]
    exact card_center_statedSp_three hodd
  obtain ⟨α, hα, hαs, hker⟩ := LieType.Steinberg.exists_surjective_of_isPerfect
    (fun E _ _ π hπ hcen _ => by
      rcases Nat.lt_or_ge (Nat.card F) 5 with h5F | h5F
      · have h3F : Nat.card F = 3 := by
          obtain ⟨k, hk⟩ := hodd
          have := Finite.one_lt_card (α := F)
          omega
        exact LieType.Steinberg.CentralExt.SpThree.sp_three_exists_section_of_central h3F le_rfl
          hπ hcen
      · exact LieType.Steinberg.CentralExt.SpClosed.sp_exists_section_of_central (by norm_num)
          h5F hπ hcen)
    hβs hη's hcen' h2'
  have hαβ : α.ker ≤ β.ker := by
    intro A hA
    rw [MonoidHom.mem_ker] at hA ⊢
    rw [← hα, hA, map_one]
  have hne : α.ker ≠ β.ker := by
    intro h1
    have hbot : η'.ker = ⊥ := by
      rw [hker, ← h1, eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    have hCN : center L ≤ N := by
      intro c hc
      have hc' : QuotientGroup.mk' N c ∈ η'.ker := by
        rw [hker']
        exact ⟨c, hηker ▸ hc, rfl⟩
      rw [hbot, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc'
      exact hc'
    have h2 : 2 ∣ Nat.card (center L) := Nat.dvd_of_factorization_pos (by rw [hZ]; norm_num)
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have h3 := (LieType.Steinberg.mem_oddPart.1 (hCN c.2)).2
    rw [Subgroup.orderOf_coe, hc] at h3
    exact (Nat.not_even_iff_odd.2 h3) even_two
  have hdvd : Nat.card α.ker ∣ Nat.card β.ker := Subgroup.card_dvd_of_le hαβ
  have h1 : Nat.card α.ker = 1 := by
    rw [hβcard] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hαβ (by rw [h, hβcard])) hne
  have hinj : Function.Injective α :=
    (MonoidHom.ker_eq_bot_iff α).1 (Subgroup.eq_bot_of_card_eq _ h1)
  exact ⟨F, inferInstance, inferInstance, hF, hp,
    ⟨(MulEquiv.ofBijective α ⟨hinj, hαs⟩).symm⟩⟩

theorem noSpin7_of_lieModel_psp_three {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    {p f : ℕ} (hp2 : p ≠ 2) (hL : Blueprint.LieModel (L ⧸ center L) .PSp 3 p f) :
    NoSpin7 p L := by
  intro r hr hZ hLM
  have hv1 := (CatLeafProof.X10Lin.lieOrder_of_lieModel_classical
    (Or.inr (Or.inr (Or.inl rfl))) hp2 (by norm_num) hL).2
  have hv2 := (CatLeafProof.X10Lin.lieOrder_of_lieModel_classical
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hp2 (by norm_num) hLM).2
  have hfr : f = r := by
    rw [hv1] at hv2
    change 9 * f = 9 * r at hv2
    omega
  rw [hfr] at hL
  obtain ⟨F, _, _, hF, hp, ⟨e⟩⟩ := exists_mulEquiv_statedSp hp2 hL hZ
  exact NoSpin7.of_quotient (LieType.Steinberg.oddPart (center L) le_rfl) (fun _ hc => hc.1)
    not_two_dvd_card_oddPart (noSpin7_of_mulEquiv_statedSp hp hp2 hF e.symm) r hr hZ hLM

theorem noSpin7_of_lieModel_ne (hO : LieOrderFormulasInput) {L : Type} [Group L] [Finite L]
    [Group.IsPerfect L] {t : StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hL : Blueprint.LieModel (L ⧸ center L) t n p f)
    (ht : ¬ (t = .POmegaOdd ∧ n = 3)) : NoSpin7 p L := by
  by_cases hC : t = .PSp ∧ n = 3
  · obtain ⟨rfl, rfl⟩ := hC
    exact noSpin7_of_lieModel_psp_three hp2 hL
  · refine noSpin7_of_lieModel hO hp2 hadm hL ?_
    rintro ⟨h1 | h1, h2⟩
    · exact ht ⟨h1, h2⟩
    · exact hC ⟨h1, h2⟩

end CFSG.ComponentClassification.HarrisLit.T1.P51e
