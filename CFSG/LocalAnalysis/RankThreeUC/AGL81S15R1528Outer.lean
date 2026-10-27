module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.SevenRank
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526I3
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526P0c
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526F1
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankBase
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515A
import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.LocalAnalysis.AGL81TheoremCD
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15
open CFSG.AGLEmbedding Subgroup KFactsPair
open scoped Pointwise

section SectionRank

variable {X : Type} [Group X] [Finite X]

theorem pRank_seven_succ_le_of_le_cMHat {L R : Subgroup X} (hL : IsC2 L)
    (h3 : IsLThreeOfExp 1 ↥(barO2 L)) (hZ : Nat.card (Subgroup.center ↥(barO2 L)) = 1) {b : ℕ}
    (hsup : CFSG.Open.pRank 7 (R ⊔ L) ≤ b) (hR : R ≤ cMHat L) :
    CFSG.Open.pRank 7 R + 1 ≤ b := by
  have hq : Nat.Prime 7 := by norm_num
  have hq2 : (7 : ℕ) ≠ 2 := by norm_num
  have hc : ∀ a ∈ barO2 R, ∀ c ∈ barO2 L, a * c = c * a := by
    rintro _ ⟨i, hi, rfl⟩ c hc
    exact (Subgroup.mem_centralizer_iff.1 (hR hi) c hc).symm
  have key := pRank_add_le_pRank_sup_add_pRank_inf hc hq
  have hinf : barO2 R ⊓ barO2 L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hz : (⟨x, hx.2⟩ : ↥(barO2 L)) ∈ Subgroup.center ↥(barO2 L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc x hx.1 g g.2).symm
    rw [Subgroup.eq_bot_of_card_eq _ hZ, Subgroup.mem_bot] at hz
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hz)
  have hbot : CFSG.Open.pRank 7 (barO2 R ⊓ barO2 L) = 0 := by
    rw [hinf]
    exact pRank_eq_zero_of_not_dvd_s15 hq (by rw [Subgroup.card_bot]; norm_num)
  have hsup' : CFSG.Open.pRank 7 (barO2 R ⊔ barO2 L) ≤ b := by
    have e : barO2 R ⊔ barO2 L = barO2 (R ⊔ L) := (Subgroup.map_sup _ _ _).symm
    rw [e, ← pRank_barO2_eq_aux_eq (R ⊔ L) hq hq2]
    exact hsup
  have hL1 : CFSG.Open.pRank 7 (barO2 L) = 1 :=
    (pRank_barO2_eq hL hq hq2).symm.trans (pRank_eq_one_of_isLThree hL h3).2
  rw [← pRank_barO2_eq_aux_eq R hq hq2] at key
  omega

end SectionRank

section QLevel

open two_le_pRank_centralizer_of_pComponent_aux

theorem false_of_three_components_split {Q R : Type} [Group Q] [Finite Q] [Group R] [Finite R]
    (μ : Q →* R) {D : Subgroup Q} (hD : μ.ker ≤ D) (hDr : CFSG.Open.pRank 7 D ≤ 1)
    (hR : CFSG.Open.pRank 7 (⊤ : Subgroup R) ≤ 2) (A : ℕ → Subgroup Q)
    (hAc : ∀ i, i < 3 → CFSG.IsComponent (A i))
    (hArank : ∀ i, i < 3 → CFSG.Open.pRank 7 (A i) = 1)
    (hAne : ∀ i j, i < 3 → j < 3 → i ≠ j → A i ≠ A j)
    (hall : (∀ i, i < 3 → A i ≤ μ.ker) ∨ (∀ i, i < 3 → ¬ A i ≤ μ.ker)) : False := by
  haveI hF7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hp7 : Nat.Prime 7 := hF7.out
  have hcomm : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a := by
    intro i j hi hj hij a ha b hb
    have hc := kComp_holds.1 _ (A i) (A j) ((CFSG.isComponent_iff_open _).1 (hAc i hi))
      ((CFSG.isComponent_iff_open _).1 (hAc j hj)) (hAne i j hi hj hij)
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc ha
    exact ((Subgroup.mem_centralizer_iff.1 h1) b hb).symm
  have hrkTop : ∀ i, i < 3 → CFSG.Open.pRank 7 (⊤ : Subgroup ↥(A i)) ≤ 1 := fun i hi =>
    ((CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 7) (A i)).symm.le).trans (hArank i hi).le
  have hZ : ∀ i, i < 3 → ∀ x ∈ A i, orderOf x = 7 → (∀ a ∈ A i, a * x = x * a) → False := by
    intro i hi x hx hxo hxc
    refine no_central_prime_of_perfect hp7 (by norm_num) (hAc i hi).1.1 (hrkTop i hi)
      (z := (⟨x, hx⟩ : ↥(A i))) ?_ ?_
    · rw [Subgroup.orderOf_mk]
      exact hxo
    · rw [Subgroup.mem_center_iff]
      intro a
      exact Subtype.ext (hxc a a.2)
  rcases hall with hin | hout
  · have h3 := pRank_ge_of_commute hp7 A 3 hcomm (fun i hi => (hArank i hi).ge) hZ 3 le_rfl
    have hsup : (Finset.range 3).sup A ≤ D :=
      Finset.sup_le fun i hi => (hin i (Finset.mem_range.1 hi)).trans hD
    have := CFSG.SectionRank.pRank_mono hp7.one_lt hsup
    omega
  · have himg : ∀ i, i < 3 → Group.IsPerfect ↥((A i).map μ) ∧
        CFSG.Open.pRank 7 ((A i).map μ) = 1 := by
      intro i hi
      let f : ↥(A i) →* R := μ.comp (A i).subtype
      have hker_cent : f.ker ≤ Subgroup.center ↥(A i) := by
        rcases CFSG.LocalCores.quasisimple_normal_subgroups (hAc i hi).1 f.normal_ker with h | h
        · exfalso
          apply hout i hi
          intro a ha
          have h1 : (⟨a, ha⟩ : ↥(A i)) ∈ f.ker := by
            rw [h]
            exact Subgroup.mem_top _
          exact h1
        · exact h
      have hker7 : ¬ 7 ∣ Nat.card f.ker := by
        intro hdvd
        obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥f.ker) 7 hdvd
        refine no_central_prime_of_perfect hp7 (by norm_num) (hAc i hi).1.1 (hrkTop i hi)
          (z := (z : ↥(A i))) ?_ (hker_cent z.2)
        rw [Subgroup.orderOf_coe]
        exact hz
      have hmap : (⊤ : Subgroup ↥(A i)).map f = (A i).map μ := by
        ext y
        constructor
        · rintro ⟨a, -, rfl⟩
          exact ⟨a, a.2, rfl⟩
        · rintro ⟨a, ha, rfl⟩
          exact ⟨⟨a, ha⟩, Subgroup.mem_top _, rfl⟩
      refine ⟨?_, ?_⟩
      · haveI : Group.IsPerfect ↥(A i) := (hAc i hi).1.1
        rw [← hmap]
        exact Group.IsPerfect.map f
      · rw [← hmap, pRank_map_eq_of_ker hp7 f hker7 ⊤,
          ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
        exact hArank i hi
    have hone : ∀ i, i < 3 → 1 ≤ CFSG.Open.pRank 7 ((A i).map μ) := fun i hi => (himg i hi).2.ge
    have hZB : ∀ i, i < 3 → ∀ x ∈ (A i).map μ, orderOf x = 7 →
        (∀ a ∈ (A i).map μ, a * x = x * a) → False := by
      intro i hi x hx hxo hxc
      refine no_central_prime_of_perfect hp7 (by norm_num) (himg i hi).1 ?_
        (z := (⟨x, hx⟩ : ↥((A i).map μ))) ?_ ?_
      · exact ((CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 7) ((A i).map μ)).symm.le).trans
          (himg i hi).2.le
      · rw [Subgroup.orderOf_mk]
        exact hxo
      · rw [Subgroup.mem_center_iff]
        intro a
        exact Subtype.ext (hxc a a.2)
    have hcommB : ∀ i j : ℕ, i < 3 → j < 3 → i ≠ j → ∀ a ∈ (A i).map μ, ∀ b ∈ (A j).map μ,
        a * b = b * a := by
      rintro i j hi hj hij _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hcomm i j hi hj hij a ha b hb]
    have h3 := pRank_ge_of_commute hp7 (fun i => (A i).map μ) 3 hcommB hone hZB 3 le_rfl
    have := CFSG.SectionRank.pRank_mono hp7.one_lt
      (le_top : (Finset.range 3).sup (fun i => (A i).map μ) ≤ ⊤)
    omega

end QLevel

section XLevel

open two_le_pRank_centralizer_of_pComponent_aux

variable {X : Type} [Group X] [Finite X]

theorem index_normalizer_le_two_of_rank_bounds {Y₀ C : Subgroup X} [Y₀.Normal] [C.Normal]
    (hQ : CFSG.Open.pRank 7 (⊤ : Subgroup (X ⧸ Y₀)) ≤ 2)
    (hD : CFSG.Open.pRank 7 (C ⊓ Y₀) ≤ 1) {I : Subgroup X} (hI : I ≤ C)
    (hIc : CFSG.IsPComponent 7 (I.subgroupOf C)) (hI1 : CFSG.Open.pRank 7 I = 1) :
    (Subgroup.normalizer (I : Set X)).index ≤ 2 := by
  haveI hF7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hp7 : Nat.Prime 7 := hF7.out
  by_contra hlt
  classical
  letI : Fintype (X ⧸ Subgroup.normalizer (I : Set X)) := Fintype.ofFinite _
  have hcard : 2 < Fintype.card (X ⧸ Subgroup.normalizer (I : Set X)) := by
    have : 2 < Nat.card (X ⧸ Subgroup.normalizer (I : Set X)) := not_le.1 hlt
    rwa [Nat.card_eq_fintype_card] at this
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 hcard
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨g₁, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨g₂, rfl⟩ := QuotientGroup.mk_surjective c
  have key : ∀ g g' : X, (QuotientGroup.mk g : X ⧸ Subgroup.normalizer (I : Set X)) ≠
      QuotientGroup.mk g' → conjSub g I ≠ conjSub g' I := fun g g' hne h =>
    hne ((QuotientGroup.eq).2 (mem_normalizer_I_of_odd_order_aux_coset h))
  have h01 := key _ _ hab
  have h02 := key _ _ hac
  have h12 := key _ _ hbc
  let g : ℕ → X := fun i => if i = 0 then g₀ else if i = 1 then g₁ else g₂
  have hg0 : g 0 = g₀ := by simp [g]
  have hg1 : g 1 = g₁ := by simp [g]
  have hg2 : g 2 = g₂ := by simp [g]
  let J : ℕ → Subgroup X := fun i => conjSub (g i) I
  have hJne : ∀ i j, i < 3 → j < 3 → i ≠ j → J i ≠ J j := by
    intro i j hi hj hij
    interval_cases i <;> interval_cases j <;>
      first
        | exact absurd rfl hij
        | (simp only [J, hg0, hg1, hg2]; first | assumption | exact Ne.symm ‹_›)
  have hJC : ∀ i, J i ≤ C ∧ CFSG.IsPComponent 7 ((J i).subgroupOf C) := fun i =>
    normal_I_of_noncyclic_aux_isPComponent_conj (g i) hI hIc
  let N : Subgroup ↥C := CFSG.pPrimeCore 7 ↥C
  let π : ↥C →* ↥C ⧸ N := QuotientGroup.mk' N
  have hker : ¬ 7 ∣ Nat.card π.ker := by
    rw [QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd hp7).1 (CFSG.pPrimeCore_coprime_card (p := 7) (G := ↥C))
  have hN7 : ¬ 7 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd hp7).1 (CFSG.pPrimeCore_coprime_card (p := 7) (G := ↥C))
  let Nh : Subgroup X := N.map C.subtype
  have hNh : Nh.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hx
    have hmap : N.map (MulAut.conjNormal g : MulAut ↥C).toMonoidHom = N :=
      CFSG.pPrimeCore_map_iso 7 (MulAut.conjNormal g : MulAut ↥C)
    have hy' : (MulAut.conjNormal g : MulAut ↥C) y ∈ N := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hy
    exact ⟨_, hy', rfl⟩
  let N' : Subgroup (X ⧸ Y₀) := Nh.map (QuotientGroup.mk' Y₀)
  haveI hN' : N'.Normal := Subgroup.Normal.map hNh _ (QuotientGroup.mk'_surjective Y₀)
  have hN'7 : ¬ 7 ∣ Nat.card N' := by
    intro hdvd
    have h1 : Nat.card N' ∣ Nat.card Nh := Subgroup.card_map_dvd Nh _
    have h2 : Nat.card Nh = Nat.card N := Subgroup.card_map_of_injective C.subtype_injective
    exact hN7 (h2 ▸ hdvd.trans h1)
  let ψ' : X →* (X ⧸ Y₀) ⧸ N' := (QuotientGroup.mk' N').comp (QuotientGroup.mk' Y₀)
  let ψ : ↥C →* (X ⧸ Y₀) ⧸ N' := ψ'.comp C.subtype
  have hNψ : N ≤ ψ.ker := by
    intro n hn
    show ψ' (n : X) = 1
    refine (QuotientGroup.eq_one_iff _).2 ?_
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem C.subtype hn)
  let μ : ↥C ⧸ N →* (X ⧸ Y₀) ⧸ N' := QuotientGroup.lift N ψ hNψ
  have hμπ : ∀ c : ↥C, μ (π c) = ψ' (c : X) := fun c => rfl
  have hRrank : CFSG.Open.pRank 7 (⊤ : Subgroup ((X ⧸ Y₀) ⧸ N')) ≤ 2 := by
    rw [CFSG.SectionRank.pRank_quotient_eq N' hN'7]
    exact hQ
  let C₀ : Subgroup ↥C := (C ⊓ Y₀).subgroupOf C
  let D : Subgroup (↥C ⧸ N) := C₀.map π
  have hC₀rank : CFSG.Open.pRank 7 C₀ = CFSG.Open.pRank 7 (C ⊓ Y₀) := by
    rw [← CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective 7
      C.subtype_injective C₀, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  have hDrank : CFSG.Open.pRank 7 D ≤ 1 := by
    have h1 : CFSG.Open.pRank 7 D ≤ CFSG.Open.pRank 7 C₀ :=
      CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hp7 π hker C₀
    rw [hC₀rank] at h1
    exact h1.trans hD
  have hkerμ : μ.ker ≤ D := by
    intro y hy
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective N y
    have h1 : ψ' (c : X) = 1 := hy
    have h2 : QuotientGroup.mk' Y₀ (c : X) ∈ N' := (QuotientGroup.eq_one_iff _).1 h1
    obtain ⟨n, hn, hnc⟩ := Subgroup.mem_map.1 h2
    obtain ⟨n', hn', rfl⟩ := hn
    have h3 : ((n'⁻¹ * c : ↥C) : X) ∈ Y₀ := by
      have := QuotientGroup.eq.1 hnc
      simpa using this
    refine ⟨n'⁻¹ * c, ⟨(n'⁻¹ * c).2, h3⟩, ?_⟩
    have h4 : π n'⁻¹ = 1 := (QuotientGroup.eq_one_iff _).2 (N.inv_mem hn')
    show π (n'⁻¹ * c) = π c
    rw [map_mul, h4, one_mul]
  let A : ℕ → Subgroup (↥C ⧸ N) := fun i => ((J i).subgroupOf C).map π
  have hAc : ∀ i, i < 3 → CFSG.IsComponent (A i) := by
    intro i hi
    obtain ⟨K, hK, -, hmap, -⟩ := (hJC i).2
    have : A i = K := hmap
    rw [this]
    exact hK
  have hrk1 : ∀ i, CFSG.Open.pRank 7 ((J i).subgroupOf C) = 1 := by
    intro i
    rw [← CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective 7
      C.subtype_injective ((J i).subgroupOf C), Subgroup.map_subgroupOf_eq_of_le (hJC i).1]
    show CFSG.Open.pRank 7 (I.map (MulAut.conj (g i)).toMonoidHom) = 1
    rw [CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective 7
      (MulAut.conj (g i)).injective, hI1]
  have hArank : ∀ i, i < 3 → CFSG.Open.pRank 7 (A i) = 1 := fun i _ =>
    (pRank_map_eq_of_ker hp7 π hker _).trans (hrk1 i)
  have hAne : ∀ i j, i < 3 → j < 3 → i ≠ j → A i ≠ A j := by
    intro i j hi hj hij heq
    have h1 := CFSG.ComponentClassification.UnbalancedLayer.pComponent_eq_of_map_eq (hJC i).2
      (hJC j).2 heq
    apply hJne i j hi hj hij
    rw [← Subgroup.map_subgroupOf_eq_of_le (hJC i).1, ← Subgroup.map_subgroupOf_eq_of_le (hJC j).1,
      h1]
  have hall : (∀ i, i < 3 → A i ≤ μ.ker) ∨ (∀ i, i < 3 → ¬ A i ≤ μ.ker) := by
    have hAi : ∀ i, A i ≤ μ.ker ↔ J i ≤ ψ'.ker := by
      intro i
      constructor
      · intro h x hx
        have hxC : x ∈ C := (hJC i).1 hx
        have h1 : π ⟨x, hxC⟩ ∈ A i := ⟨⟨x, hxC⟩, hx, rfl⟩
        exact h h1
      · intro h y hy
        obtain ⟨c, hc, rfl⟩ := hy
        exact h hc
    have hJi : ∀ i, J i ≤ ψ'.ker ↔ I ≤ ψ'.ker := by
      intro i
      constructor
      · intro h a ha
        have h1 : ψ' (g i) * ψ' a * (ψ' (g i))⁻¹ = 1 := by
          rw [← map_inv, ← map_mul, ← map_mul]
          exact h ⟨a, ha, rfl⟩
        show ψ' a = 1
        calc ψ' a = (ψ' (g i))⁻¹ * (ψ' (g i) * ψ' a * (ψ' (g i))⁻¹) * ψ' (g i) := by group
          _ = 1 := by rw [h1]; group
      · rintro h _ ⟨a, ha, rfl⟩
        have h1 : ψ' a = 1 := h ha
        show ψ' (g i * a * (g i)⁻¹) = 1
        rw [map_mul, map_mul, map_inv, h1, mul_one, mul_inv_cancel]
    by_cases hI' : I ≤ ψ'.ker
    · exact Or.inl fun i _ => (hAi i).2 ((hJi i).2 hI')
    · exact Or.inr fun i _ h => hI' ((hJi i).1 ((hAi i).1 h))
  exact false_of_three_components_split μ hkerμ hDrank hRrank A hAc hArank hAne hall

end XLevel

section Row1527

theorem mem_of_odd_order_of_index_le_two {X : Type} [Group X] [Finite X] {N : Subgroup X}
    (hidx : N.index ≤ 2) {x : X} (hx : Odd (orderOf x)) : x ∈ N := by
  have hpos : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hsq : x ^ 2 ∈ N := by
    rcases (by omega : N.index = 1 ∨ N.index = 2) with h1 | h2
    · rw [Subgroup.index_eq_one.1 h1]
      exact Subgroup.mem_top _
    · haveI := Subgroup.normal_of_index_eq_two h2
      have := Subgroup.pow_index_mem N x
      rwa [h2] at this
  obtain ⟨m, hm⟩ := hx
  have : x = (x ^ 2) ^ (m + 1) := by
    rw [← pow_mul]
    calc x = x ^ (orderOf x) * x := by rw [pow_orderOf_eq_one, one_mul]
      _ = x ^ (2 * (m + 1)) := by rw [← pow_succ, hm]; ring_nf
  rw [this]
  exact Subgroup.pow_mem _ hsq m.succ

theorem index_normalizer_I_le_two_of_row1527 (hKSML3 : KSML3) {G : Type} [Group G] [Finite G]
    {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂)
    (h7 : 7 ∈ sigmaSet G M) (h27 : Row1527 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hLn : L.Normal) {I : Subgroup ↥M} (hI : I ≤ cMHat L)
    (hIc : CFSG.IsPComponent 7 (I.subgroupOf (cMHat L))) (hI1 : CFSG.Open.pRank 7 I = 1) :
    (Subgroup.normalizer (I : Set ↥M)).index ≤ 2 := by
  have hS : IsSimpleGroup ↥(Ystar (T.subgroupOf M) T₁ T₂) := hLN_aux_isSimpleGroup h27
  have hLsY : Ls = Ystar (T.subgroupOf M) T₁ T₂ := hLN_aux_eq_ystar_of_simple hS hLs
  have h3 : IsLThreeOfExp 1 ↥Ls := by
    rw [hLsY]
    exact h27
  have hY : (Y0 (T.subgroupOf M) T₁ T₂).Normal :=
    (ystar_normal_of_row1527 ctx h7 h27).comap (toStar (T.subgroupOf M))
  haveI := hY
  have hQ := pRank_quotient_Y0_le_two ctx.factor hY Nat.prime_seven (by norm_num)
    (ctx.rank_N₁ 7 h7) (ctx.rank_N₂ 7 h7)
  have hY0 : CFSG.Open.pRank 7 (Y0 (T.subgroupOf M) T₁ T₂) ≤ 2 := by
    change CFSG.Open.pRank 7 ((Ystar (T.subgroupOf M) T₁ T₂).comap (toStar (T.subgroupOf M))) ≤ 2
    have h1 := pRank_comap_toStar_le (X := ↥M) (T := T.subgroupOf M) (p := 7) Nat.prime_seven
      (Ystar (T.subgroupOf M) T₁ T₂)
    have hC : CFSG.Open.pRank 7 (gnC (T.subgroupOf M)) ≤ 1 := ctx.rank_C 7 h7
    have hYs : CFSG.Open.pRank 7 (Ystar (T.subgroupOf M) T₁ T₂) ≤ 1 := by
      rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      exact pRank_seven_le_one_of_isLThreeOfExp_one h27
    omega
  obtain ⟨hbar, hZ⟩ := barO2_isLThree_of_lift hKSML3 ctx.gn hLs.1 hL h3
  have hLY : L ≤ Y0 (T.subgroupOf M) T₁ T₂ := by
    intro x hx
    change toStar (T.subgroupOf M) x ∈ Ystar (T.subgroupOf M) T₁ T₂
    rw [← hLsY, ← hL.2]
    exact Subgroup.mem_map_of_mem _ hx
  haveI : (cMHat L).Normal := cMHat_normal hLn
  have hD : CFSG.Open.pRank 7 (cMHat L ⊓ Y0 (T.subgroupOf M) T₁ T₂) ≤ 1 := by
    have h1 := pRank_seven_succ_le_of_le_cMHat (L := L)
      (R := cMHat L ⊓ Y0 (T.subgroupOf M) T₁ T₂) hL.1 hbar hZ (b := 2)
      ((CFSG.SectionRank.pRank_mono Nat.prime_seven.one_lt (sup_le inf_le_right hLY)).trans hY0)
      inf_le_left
    omega
  exact index_normalizer_le_two_of_rank_bounds hQ hD hI hIc hI1

theorem mem_normalizer_I_of_odd_order_of_row1527 (hKSML3 : KSML3) {G : Type} [Group G] [Finite G]
    {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂)
    (h7 : 7 ∈ sigmaSet G M) (h27 : Row1527 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hLn : L.Normal) {I : Subgroup ↥M} (hI : I ≤ cMHat L)
    (hIc : CFSG.IsPComponent 7 (I.subgroupOf (cMHat L))) (hI1 : CFSG.Open.pRank 7 I = 1)
    {x : ↥M} (hx : Odd (orderOf x)) : x ∈ Subgroup.normalizer (I : Set ↥M) :=
  mem_of_odd_order_of_index_le_two
    (index_normalizer_I_le_two_of_row1527 hKSML3 ctx h7 h27 hLs hL hLn hI hIc hI1) hx

theorem mem_normalizer_I_of_three_pow_of_row1527 (hKSML3 : KSML3) {G : Type} [Group G] [Finite G]
    {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂)
    (h7 : 7 ∈ sigmaSet G M) (h27 : Row1527 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hLn : L.Normal) {I : Subgroup ↥M} (hI : I ≤ cMHat L)
    (hIc : CFSG.IsPComponent 7 (I.subgroupOf (cMHat L))) (hI1 : CFSG.Open.pRank 7 I = 1) :
    ∀ x : ↥M, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ Subgroup.normalizer (I : Set ↥M) :=
  fun _ ⟨_, hk⟩ => mem_normalizer_I_of_odd_order_of_row1527 hKSML3 ctx h7 h27 hLs hL hLn hI hIc hI1
    (by rw [hk]; exact Odd.pow (by decide))

end Row1527

end CFSG.LocalAnalysis.RankThreeUC.S15
