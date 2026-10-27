module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalThirteen
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalFiveLift
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalFiveStar

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix DeltaLocal.Five

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem eq_one_of_mem_factor_zStar_conj (hC : Counterexample G D r Abar) {a : Fin r} {g : G}
    (hg : g ∉ Subgroup.normalizer (D : Set G)) {t : G}
    (htA : t ∈ aschbacherThm5Preimage D (Abar a))
    (htZ : t ∈ rightConjugate (zStar D Abar) g) (ht2 : ∃ k : ℕ, t ^ (2 ^ k) = 1) : t = 1 := by
  by_contra ht1
  obtain ⟨b, hba⟩ := exists_other hC a
  have h1 := cross_factor_centralizes D Abar hC.hyp.hcomm b a hba t htA
  rw [mem_rightConjugate_iff] at htZ
  have h2 := (mem_zStar_iff.mp htZ).2 a
  have h3 := mem_normalizer_of_fusion hC b a (t := t) (g := g⁻¹) ht2 ht1 h1 (by simpa using h2)
  exact hg (by simpa using (Subgroup.normalizer (D : Set G)).inv_mem h3)

theorem odd_card_zStar_conj_inf (hC : Counterexample G D r Abar) {a : Fin r} {g : G}
    (hg : g ∉ Subgroup.normalizer (D : Set G)) :
    Odd (Nat.card (rightConjugate (zStar D Abar) g ⊓ aschbacherThm5Preimage D (Abar a) :
      Subgroup G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra heven
  rw [Nat.not_odd_iff_even] at heven
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
  have hx' : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have h1 := eq_one_of_mem_factor_zStar_conj hC hg x.2.2 x.2.1
    ⟨1, by rw [pow_one, ← hx']; exact pow_orderOf_eq_one _⟩
  rw [h1, orderOf_one] at hx'
  omega

theorem comm_of_mem_S_inf (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a)
    (hUZ : AschbacherTheorem3.omegaOne d.T ≤ rightConjugate (zStar D Abar) d.g) {s u : G}
    (hs : s ∈ d.S ⊓ rightConjugate (Subgroup.normalizer (D : Set G)) d.g)
    (hu : u ∈ AschbacherTheorem3.omegaOne d.T) : s * u = u * s := by
  have hHgZ : rightConjugate (Subgroup.normalizer (D : Set G)) d.g ≤
      Subgroup.normalizer (rightConjugate (zStar D Abar) d.g : Set G) :=
    AschbacherTheorem3.rightConjugate_le_normalizer (normalizer_le_normalizer_zStar hC.hyp) d.g
  have hc1 : s⁻¹ * u⁻¹ * s * u ∈ rightConjugate (zStar D Abar) d.g := by
    have h1 : s⁻¹ * u⁻¹ * s ∈ rightConjugate (zStar D Abar) d.g := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hHgZ hs.2)) u⁻¹).mp
        (Subgroup.inv_mem _ (hUZ hu))
      simpa [mul_assoc] using this
    exact Subgroup.mul_mem _ h1 (hUZ hu)
  have hc2 : s⁻¹ * u⁻¹ * s * u ∈ d.S := by
    have h1 : u⁻¹ * s * u ∈ d.S := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _
        (EndHyp.U_le_normalizer_S hu)) s).mp hs.1
      simpa [mul_assoc] using this
    have : s⁻¹ * u⁻¹ * s * u = s⁻¹ * (u⁻¹ * s * u) := by group
    rw [this]
    exact d.S.mul_mem (d.S.inv_mem hs.1) h1
  have hc := eq_one_of_mem_factor_zStar_conj hC (datum_g_not_mem d) (d.sylowS.le hc2) hc1
    (twoElt_of_mem d.sylowS.isPGroup hc2)
  calc s * u = u * s * (s⁻¹ * u⁻¹ * s * u) := by group
    _ = u * s := by rw [hc, mul_one]

theorem S_inf_centralizer_eq (hC : Counterexample G D r Abar) {a : Fin r}
    (d : DeltaDatum D Abar a)
    (hUZ : AschbacherTheorem3.omegaOne d.T ≤ rightConjugate (zStar D Abar) d.g) {u : G}
    (hu : u ∈ AschbacherTheorem3.omegaOne d.T) (hu1 : u ≠ 1) :
    d.S ⊓ Subgroup.centralizer {u} =
      d.S ⊓ rightConjugate (Subgroup.normalizer (D : Set G)) d.g := by
  apply le_antisymm
  · exact inf_le_inf_left _ (centralizer_le_of_mem_zStar_conj hC d.g (hUZ hu)
      (twoElt_of_mem (d.sylowT.isPGroup.to_le EndHyp.U_le_T) hu) hu1)
  · intro s hs
    exact ⟨hs.1, Subgroup.mem_centralizer_singleton_iff.mpr
      (comm_of_mem_S_inf hC d hUZ hs hu)⟩

theorem normalizer_U_le (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a)
    (hUZ : AschbacherTheorem3.omegaOne d.T ≤ rightConjugate (zStar D Abar) d.g)
    (hU1 : AschbacherTheorem3.omegaOne d.T ≠ ⊥) :
    Subgroup.normalizer (AschbacherTheorem3.omegaOne d.T : Set G) ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) d.g := by
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  intro x hx
  have hux : x⁻¹ * u * x ∈ AschbacherTheorem3.omegaOne d.T := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) u).mp hu
    simpa using this
  exact mem_conj_normalizer_of_zStar hC d.g (hUZ hu) (hUZ hux)
    (twoElt_of_mem (d.sylowT.isPGroup.to_le EndHyp.U_le_T) hu) hu1'

omit [Finite G] in
theorem sup_inf_eq_of_le {X Y M : Subgroup G} (hYX : Y ≤ Subgroup.normalizer (X : Set G))
    (hYM : Y ≤ M) : (X ⊔ Y) ⊓ M = (X ⊓ M) ⊔ Y := by
  apply le_antisymm
  · intro x ⟨hx, hxM⟩
    have hx' : x ∈ ((X ⊔ Y : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left X Y hYX] at hx'
    obtain ⟨x₁, hx₁, y, hy, rfl⟩ := Set.mem_mul.mp hx'
    have hx₁M : x₁ ∈ M := by
      have : x₁ = x₁ * y * y⁻¹ := by group
      rw [this]
      exact M.mul_mem hxM (M.inv_mem (hYM hy))
    exact Subgroup.mul_mem_sup ⟨hx₁, hx₁M⟩ hy
  · exact sup_le (inf_le_inf_right M le_sup_left) (le_inf le_sup_right hYM)

theorem frame_U (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a) :
    AschbacherTheorem3.Frame (aschbacherThm5Preimage D (Abar a))
      (AschbacherTheorem3.omegaOne d.T) :=
  ⟨EndHyp.U_le_normalizer_A, EndHyp.U_inf_A hC, d.sylowT.isPGroup.to_le EndHyp.U_le_T⟩

theorem sylowFrame_U (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a)
    (hUZ : AschbacherTheorem3.omegaOne d.T ≤ rightConjugate (zStar D Abar) d.g)
    (hU1 : AschbacherTheorem3.omegaOne d.T ≠ ⊥) :
    AschbacherTheorem3.SylowFrame (aschbacherThm5Preimage D (Abar a))
      (AschbacherTheorem3.omegaOne d.T) (d.S ⊔ AschbacherTheorem3.omegaOne d.T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set Hg := rightConjugate (Subgroup.normalizer (D : Set G)) d.g with hHgdef
  set N := Subgroup.normalizer (U : Set G) with hNdef
  have hF := frame_U hC d
  have hU2 : IsPGroup 2 U := d.sylowT.isPGroup.to_le EndHyp.U_le_T
  have hS0N : d.S ⊓ Hg ≤ N := fun s hs => Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun u hu => (comm_of_mem_S_inf hC d hUZ hs hu).symm)
  have hS0 : IsSylowOf 2 (d.S ⊓ Hg) (A ⊓ N) :=
    d.sylowInter.of_le (le_inf (inf_le_left.trans d.sylowS.le) hS0N)
      (inf_le_inf_left A (normalizer_U_le hC d hUZ hU1))
  have hUAN : U ≤ Subgroup.normalizer ((A ⊓ N : Subgroup G) : Set G) := fun u hu =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨EndHyp.U_le_normalizer_A hu,
      Subgroup.le_normalizer (Subgroup.le_normalizer hu)⟩
  have hF' : AschbacherTheorem3.Frame (A ⊓ N) U :=
    ⟨hUAN, le_bot_iff.mp ((inf_le_inf_left U inf_le_left).trans (EndHyp.U_inf_A hC).le),
      hU2⟩
  have hUS0 : U ≤ Subgroup.normalizer ((d.S ⊓ Hg : Subgroup G) : Set G) := fun u hu =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨EndHyp.U_le_normalizer_S hu,
      (EndHyp.U_le_L hu |> fun h => Subgroup.le_normalizer (conj_factor_le a d.g h))⟩
  have h1 := AschbacherTheorem3.isSylowOf_sup_of_frame hF' hS0 hUS0
  have hmod : (A ⊔ U) ⊓ N = (A ⊓ N) ⊔ U :=
    sup_inf_eq_of_le EndHyp.U_le_normalizer_A Subgroup.le_normalizer
  have hSU2 : IsPGroup 2 (d.S ⊔ U : Subgroup G) := by
    rw [sup_comm]
    exact IsPGroup.to_sup_of_normal_right' hU2 d.sylowS.isPGroup EndHyp.U_le_normalizer_S
  refine ⟨hF, ?_, ?_⟩
  · have h2 := AschbacherTheorem3.isSylowOf_sup_of_frame hF d.sylowS EndHyp.U_le_normalizer_S
    rwa [sup_comm] at h2
  · rw [hmod]
    have heq := h1.eq_of_le (le_inf (sup_le le_sup_right (inf_le_left.trans le_sup_left))
      (sup_le Subgroup.le_normalizer hS0N))
      (by rw [← hmod]; exact inf_le_inf_right N (sup_le_sup_right d.sylowS.le U))
      (hSU2.to_le inf_le_left)
    rw [heq]
    exact h1

theorem hyp43_U (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a)
    (hUZ : AschbacherTheorem3.omegaOne d.T ≤ rightConjugate (zStar D Abar) d.g) :
    AschbacherTheorem3.Hyp43 (aschbacherThm5Preimage D (Abar a))
      (AschbacherTheorem3.omegaOne d.T)
      ((rightConjugate (zStar D Abar) d.g ⊓ aschbacherThm5Preimage D (Abar a)) ⊔
        AschbacherTheorem3.omegaOne d.T)
      ((aschbacherThm5Preimage D (Abar a) ⊓
        rightConjugate (Subgroup.normalizer (D : Set G)) d.g) ⊔
          AschbacherTheorem3.omegaOne d.T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set Hg := rightConjugate (Subgroup.normalizer (D : Set G)) d.g with hHgdef
  set P := rightConjugate (zStar D Abar) d.g ⊓ A with hPdef
  have hU2 : IsPGroup 2 U := d.sylowT.isPGroup.to_le EndHyp.U_le_T
  have hZg : rightConjugate (zStar D Abar) d.g ≤ Hg :=
    AschbacherTheorem3.rightConjugate_le_rightConjugate zStar_le_normalizer d.g
  have hHgN : Hg ≤ Subgroup.normalizer (rightConjugate (zStar D Abar) d.g : Set G) :=
    AschbacherTheorem3.rightConjugate_le_normalizer (normalizer_le_normalizer_zStar hC.hyp) d.g
  have hUP : U ≤ Subgroup.normalizer (P : Set G) := fun u hu =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hUZ hu),
      EndHyp.U_le_normalizer_A hu⟩
  have hPU : P ⊓ U = ⊥ := le_bot_iff.mp ((inf_le_inf_right U inf_le_right).trans
    (by rw [inf_comm]; exact (EndHyp.U_inf_A hC).le))
  have hnorm : (A ⊓ Hg) ⊔ U ≤ Subgroup.normalizer ((P ⊔ U : Subgroup G) : Set G) := by
    refine sup_le (fun x hx => ?_) (le_sup_right.trans Subgroup.le_normalizer)
    have hxA : x ∈ A := hx.1
    have hxHg : x ∈ Hg := hx.2
    apply AschbacherToolkit.mem_normalizer_of_conj_le
    have hle : P ⊔ U ≤ (P ⊔ U).comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (fun p hp => ?_) (fun e he => ?_)
      · rw [Subgroup.mem_comap]
        show x * p * x⁻¹ ∈ P ⊔ U
        exact Subgroup.mem_sup_left ⟨(Subgroup.mem_normalizer_iff.mp (hHgN hxHg) p).mp hp.1,
          (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hxA) p).mp hp.2⟩
      · rw [Subgroup.mem_comap]
        show x * e * x⁻¹ ∈ P ⊔ U
        have h1 : x * e * x⁻¹ * e⁻¹ ∈ P := by
          refine ⟨Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hHgN hxHg) e).mp
            (hUZ he)) (Subgroup.inv_mem _ (hUZ he)), ?_⟩
          have h2 := (Subgroup.mem_normalizer_iff.mp (EndHyp.U_le_normalizer_A he) x⁻¹).mp
            (Subgroup.inv_mem _ hxA)
          have h3 := Subgroup.mul_mem _ hxA h2
          rwa [show x * (e * x⁻¹ * e⁻¹) = x * e * x⁻¹ * e⁻¹ by group] at h3
        have := Subgroup.mul_mem_sup h1 he
        simpa using this
    exact fun y hy => hle hy
  have hodd : Odd (Nat.card P) := odd_card_zStar_conj_inf hC (datum_g_not_mem d)
  have hti : ∀ c ∈ A, c ∉ (A ⊓ Hg) ⊔ U → U ⊓ rightConjugate U c = ⊥ := fun c hc hcH =>
    U_inf_conj hC d (fun h => hcH (Subgroup.mem_sup_left ⟨hc, h⟩))
  exact
    { le := sup_le_sup_right (le_inf (inf_le_right) (inf_le_left.trans hZg)) U
      le_normalizer := hnorm
      le_sup := sup_le_sup_right inf_le_left U
      sylow := isSylowOf_sup_of_odd hUP hodd hU2 hPU
      inf_eq_bot := hti }

theorem H4_inf_S4 (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a) :
    ((aschbacherThm5Preimage D (Abar a) ⊓ rightConjugate (Subgroup.normalizer (D : Set G)) d.g) ⊔
        AschbacherTheorem3.omegaOne d.T) ⊓ (d.S ⊔ AschbacherTheorem3.omegaOne d.T) =
      (d.S ⊓ rightConjugate (Subgroup.normalizer (D : Set G)) d.g) ⊔
        AschbacherTheorem3.omegaOne d.T := by
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set Hg := rightConjugate (Subgroup.normalizer (D : Set G)) d.g with hHgdef
  have hUHg : U ≤ Hg := EndHyp.U_le_L.trans (conj_factor_le a d.g)
  have hUAH : U ≤ Subgroup.normalizer ((A ⊓ Hg : Subgroup G) : Set G) := fun u hu =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨EndHyp.U_le_normalizer_A hu,
      Subgroup.le_normalizer (hUHg hu)⟩
  apply le_antisymm
  · intro x ⟨hx1, hx2⟩
    have hx1' : x ∈ (((A ⊓ Hg) ⊔ U : Subgroup G) : Set G) := hx1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (A ⊓ Hg) U hUAH] at hx1'
    obtain ⟨y, hy, u, hu, rfl⟩ := Set.mem_mul.mp hx1'
    have hx2' : y * u ∈ ((d.S ⊔ U : Subgroup G) : Set G) := hx2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left d.S U EndHyp.U_le_normalizer_S] at hx2'
    obtain ⟨s, hs, u', hu', hsu⟩ := Set.mem_mul.mp hx2'
    have hmem : u' * u⁻¹ ∈ U ⊓ A := by
      refine ⟨U.mul_mem hu' (U.inv_mem hu), ?_⟩
      have : u' * u⁻¹ = s⁻¹ * y := by
        calc u' * u⁻¹ = s⁻¹ * (s * u') * u⁻¹ := by group
          _ = s⁻¹ * (y * u) * u⁻¹ := by rw [hsu]
          _ = s⁻¹ * y := by group
      rw [this]
      exact A.mul_mem (A.inv_mem (d.sylowS.le hs)) hy.1
    rw [EndHyp.U_inf_A hC, Subgroup.mem_bot] at hmem
    have hyS : y = s := by
      have hu'u : u' = u := by
        calc u' = u' * u⁻¹ * u := by group
          _ = u := by rw [hmem, one_mul]
      calc y = y * u * u⁻¹ := by group
        _ = s * u' * u⁻¹ := by rw [hsu]
        _ = s := by rw [hu'u]; group
    exact Subgroup.mul_mem_sup ⟨hyS ▸ hs, hy.2⟩ hu
  · exact sup_le (le_inf (le_sup_of_le_left (inf_le_inf_right Hg d.sylowS.le))
      (le_sup_of_le_left inf_le_left)) (le_inf le_sup_right le_sup_right)

theorem relativeWeakClosure_U (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    {a : Fin r} (d : DeltaDatum D Abar a) (hT : IsMulCommutative d.T)
    (hW : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G))
    (hcard : Nat.card (AschbacherTheorem3.omegaOne d.T) = Nat.card (AschbacherTheorem3.omegaOne
      (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))))
    {b : G} (hbS : b ∈ d.S) (hbH : b ∉ rightConjugate (Subgroup.normalizer (D : Set G)) d.g)
    (hbU : rightConjugate (AschbacherTheorem3.omegaOne d.T) b ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) d.g) :
    CFSG.SignalizerFunctor.Helpers.relativeWeakClosure (aschbacherThm5Preimage D (Abar a))
      (AschbacherTheorem3.omegaOne d.T)
      (((aschbacherThm5Preimage D (Abar a) ⊓
        rightConjugate (Subgroup.normalizer (D : Set G)) d.g) ⊔
          AschbacherTheorem3.omegaOne d.T) ⊓ (d.S ⊔ AschbacherTheorem3.omegaOne d.T)) =
      AschbacherTheorem3.omegaOne d.T ⊔ rightConjugate (AschbacherTheorem3.omegaOne d.T) b := by
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  set Hg := rightConjugate (Subgroup.normalizer (D : Set G)) d.g with hHgdef
  set W := d.S ⊓ Subgroup.normalizer (rightConjugate A d.g : Set G) with hWdef
  set V := AschbacherTheorem3.omegaOne W with hVdef
  have hU4 := four_le_card_U hloc hC d
  have hUV := sup_conj_eq hloc hC d hT hW hcard hbS hbH hbU
  rw [H4_inf_S4 hC d]
  have hVS0 : V ≤ d.S ⊓ Hg := (AschbacherTheorem3.omegaOne_le W).trans
    (inf_le_inf_left d.S (normalizer_conj_le hC a d.g))
  apply le_antisymm
  · refine iSup_le fun c => iSup_le fun hc => ?_
    have heq : CFSG.SignalizerFunctor.Helpers.conjugateSubgroup (c : G) U =
        rightConjugate U (c : G)⁻¹ := by
      unfold rightConjugate
      rw [inv_inv]
    rw [heq] at hc ⊢
    rw [← hUV]
    exact conj_le_sup hloc hC d hT hU4 (A.inv_mem c.2)
      (hc.trans (sup_le_sup_right inf_le_left U))
      (hc.trans (sup_le inf_le_right (EndHyp.U_le_L.trans (conj_factor_le a d.g))))
  · refine sup_le (CFSG.SignalizerFunctor.Helpers.subgroup_le_relative_weak_closure _ _ _
      le_sup_right) ?_
    apply AschbacherTheorem3.rightConjugate_le_relativeWeakClosure (d.sylowS.le hbS)
    calc rightConjugate U b ≤ U ⊔ rightConjugate U b := le_sup_right
      _ = U ⊔ V := hUV.symm
      _ ≤ (d.S ⊓ Hg) ⊔ U := sup_le le_sup_right (hVS0.trans le_sup_left)

theorem hyp45_U (hloc : SectionSixLocalResults) (hC : Counterexample G D r Abar)
    {a : Fin r} (d : DeltaDatum D Abar a) (hT : IsMulCommutative d.T)
    (hW : IsMulCommutative (d.S ⊓ Subgroup.normalizer
      (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G) : Subgroup G))
    (hcard : Nat.card (AschbacherTheorem3.omegaOne d.T) = Nat.card (AschbacherTheorem3.omegaOne
      (d.S ⊓ Subgroup.normalizer
        (rightConjugate (aschbacherThm5Preimage D (Abar a)) d.g : Set G))))
    (hUZ : AschbacherTheorem3.omegaOne d.T ≤ rightConjugate (zStar D Abar) d.g)
    {b : G} (hbS : b ∈ d.S) (hbH : b ∉ rightConjugate (Subgroup.normalizer (D : Set G)) d.g)
    (hbU : rightConjugate (AschbacherTheorem3.omegaOne d.T) b ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) d.g) :
    AschbacherTheorem3.Hyp45 (aschbacherThm5Preimage D (Abar a))
      (AschbacherTheorem3.omegaOne d.T) (d.S ⊔ AschbacherTheorem3.omegaOne d.T)
      ((rightConjugate (zStar D Abar) d.g ⊓ aschbacherThm5Preimage D (Abar a)) ⊔
        AschbacherTheorem3.omegaOne d.T)
      ((aschbacherThm5Preimage D (Abar a) ⊓
        rightConjugate (Subgroup.normalizer (D : Set G)) d.g) ⊔
          AschbacherTheorem3.omegaOne d.T) b := by
  have hU4 := four_le_card_U hloc hC d
  have hU1 : AschbacherTheorem3.omegaOne d.T ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hU4
    omega
  refine ⟨sylowFrame_U hC d hUZ hU1, hyp43_U hC d hUZ, d.sylowS.le hbS, ?_,
    relativeWeakClosure_U hloc hC d hT hW hcard hbS hbH hbU⟩
  intro heq
  have h1 := U_inf_conj hC d hbH
  rw [heq, inf_idem] at h1
  exact hU1 h1

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
