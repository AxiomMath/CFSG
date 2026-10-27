module

public import CFSG.CGT.PushingUpLit.SolKAb.Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25
import CFSG.CGT.PushingUpLit.SolKAb.CyclicTI
import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma25
import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Simple
import CFSG.RankThree.GF2n.Tim78Critical
import CFSG.RankThree.GF2n.Tim78Frattini
import CFSG.RankThree.GF2n.Tim78Normal
import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.CGT.PushingUpLit.SolKAb

open CFSG CFSG.CGT.Timmesfeld75 CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AschbacherKnownGroup CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Tim78
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25 WeaklyClosedInNormalizer
  not_inZStar_of_simple)

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem hasDihedralSylowTwo_transfer {X Y : Type*} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) (h : HasDihedralSylowTwo X) : HasDihedralSylowTwo Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, n, hn, ⟨eP⟩⟩ := h
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  refine ⟨P.mapSurjective hsurj, n, hn, ⟨?_⟩⟩
  exact ((P : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective).symm.trans eP

theorem hasSemidihedralSylowTwo_transfer {X Y : Type*} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) (h : HasSemidihedralSylowTwo X) : HasSemidihedralSylowTwo Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, n, hn, ⟨eP⟩⟩ := h
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  refine ⟨P.mapSurjective hsurj, n, hn, ⟨?_⟩⟩
  exact ((P : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective).symm.trans eP

theorem sq_mem_pCore_of_commutator_centralizes {M : Subgroup G}
    (hF : generalizedFitting M = pCore 2 M) {x : G} (hxM : x ∈ M)
    (hcc : ∀ q ∈ inSubgroup (pCore 2) M, (q⁻¹ * x * q * x⁻¹) * x = x * (q⁻¹ * x * q * x⁻¹)) :
    x ^ 2 ∈ inSubgroup (pCore 2) M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := inSubgroup (pCore 2) M with hQdef
  obtain ⟨hQ2, hQM, hMQ⟩ := inSubgroup_pCore_two M
  have hCQ := inf_centralizer_le_of_generalizedFitting_eq hF
  have hΦN : ∀ m ∈ M, m ∈ Subgroup.normalizer ((inSubgroup frattini Q : Subgroup G) : Set G) :=
    fun m hm => mem_normalizer_inSubgroup_frattini (hMQ hm)
  have hβ : ∀ s ∈ Q, s⁻¹ * (x ^ 2 * s * (x ^ 2)⁻¹) ∈ inSubgroup frattini Q := by
    intro s hs
    have hxs : x * s * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hMQ hxM) s).mp hs
    have hu : s⁻¹ * x * s * x⁻¹ ∈ Q := by
      have : s⁻¹ * x * s * x⁻¹ = s⁻¹ * (x * s * x⁻¹) := by group
      rw [this]; exact Q.mul_mem (Q.inv_mem hs) hxs
    have hc := hcc s hs
    have hxu : x * (s⁻¹ * x * s * x⁻¹) * x⁻¹ = s⁻¹ * x * s * x⁻¹ := by
      calc x * (s⁻¹ * x * s * x⁻¹) * x⁻¹ = ((s⁻¹ * x * s * x⁻¹) * x) * x⁻¹ := by rw [hc]
        _ = s⁻¹ * x * s * x⁻¹ := by group
    have key : s⁻¹ * (x ^ 2 * s * (x ^ 2)⁻¹) = (s⁻¹ * x * s * x⁻¹) ^ 2 := by
      have e1 : s⁻¹ * (x ^ 2 * s * (x ^ 2)⁻¹) =
          s⁻¹ * (x * (s * (s⁻¹ * x * s * x⁻¹)) * x⁻¹) := by rw [sq]; group
      have e2 : x * (s * (s⁻¹ * x * s * x⁻¹)) * x⁻¹ =
          (x * s * x⁻¹) * (x * (s⁻¹ * x * s * x⁻¹) * x⁻¹) := by group
      rw [e1, e2, hxu, sq]; group
    rw [key]
    exact sq_mem_inSubgroup_frattini hQ2 hu
  let T : Subgroup G :=
    { carrier := {m | m ∈ M ∧ ∀ s ∈ Q, s⁻¹ * (m * s * m⁻¹) ∈ inSubgroup frattini Q}
      one_mem' := by
        refine ⟨M.one_mem, fun s _ => ?_⟩
        rw [one_mul, inv_one, mul_one, inv_mul_cancel]
        exact Subgroup.one_mem _
      mul_mem' := by
        rintro m₁ m₂ ⟨hm₁, h₁⟩ ⟨hm₂, h₂⟩
        refine ⟨M.mul_mem hm₁ hm₂, fun s hs => ?_⟩
        have hs' := Tim78.conj_mem_of_mem_normalizer (hMQ hm₂) hs
        have e : s⁻¹ * (m₁ * m₂ * s * (m₁ * m₂)⁻¹) =
            (s⁻¹ * (m₁ * s * m₁⁻¹)) * (m₁ * (s⁻¹ * (m₂ * s * m₂⁻¹)) * m₁⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ (h₁ s hs)
          ((Subgroup.mem_normalizer_iff.mp (hΦN m₁ hm₁) _).mp (h₂ s hs))
      inv_mem' := by
        rintro m ⟨hm, h⟩
        refine ⟨M.inv_mem hm, fun s hs => ?_⟩
        have hs' : m⁻¹ * s * m ∈ Q := by
          have := Tim78.conj_mem_of_mem_normalizer (hMQ (M.inv_mem hm)) hs
          simpa using this
        have h1 := h _ hs'
        have e : s⁻¹ * (m⁻¹ * s * m⁻¹⁻¹) = ((m⁻¹ * s * m)⁻¹ * (m * (m⁻¹ * s * m) * m⁻¹))⁻¹ := by
          group
        rw [e]
        exact Subgroup.inv_mem _ h1 }
  have hTM : T ≤ M := fun m hm => hm.1
  have hMT : M ≤ Subgroup.normalizer (T : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun m hm => ⟨M.mul_mem (M.mul_mem hg hm.1)
      (M.inv_mem hg), fun s hs => ?_⟩
    have hs' : g⁻¹ * s * g ∈ Q := by
      have := Tim78.conj_mem_of_mem_normalizer (hMQ (M.inv_mem hg)) hs
      simpa using this
    have h1 := hm.2 _ hs'
    have e : s⁻¹ * (g * m * g⁻¹ * s * (g * m * g⁻¹)⁻¹) =
        g * ((g⁻¹ * s * g)⁻¹ * (m * (g⁻¹ * s * g) * m⁻¹)) * g⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hΦN g hg) _).mp h1
  have hyT : x ^ 2 ∈ T := ⟨M.pow_mem hxM 2, hβ⟩
  have hodd : ∀ c ∈ T, ∀ r : ℕ, r.Prime → r ≠ 2 → orderOf c = r → False := by
    intro c hcT r hr hr2 hcr
    have hcM := hTM hcT
    have hcQ : ∀ s ∈ Q, c * s = s * c :=
      commute_of_trivial_on_frattini hQ2 (hMQ hcM) hr hr2 hcr fun k s hs =>
        (T.zpow_mem hcT k).2 s hs
    have hcQ' : c ∈ Q := hCQ ⟨hcM, Subgroup.mem_centralizer_iff.mpr fun q hq => (hcQ q hq).symm⟩
    have := eq_one_of_odd_of_isPGroup hQ2 hcQ' (by rw [hcr]; exact hr.odd_of_ne_two hr2)
    rw [this, orderOf_one] at hcr
    exact hr.one_lt.ne' hcr.symm
  have hT2 : IsPGroup 2 T := by
    intro t
    obtain ⟨a, ha, -⟩ := exists_odd_orderOf_pow (t : G)
    refine ⟨a, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    set u := (t : G) ^ 2 ^ a with hu
    have huT : u ∈ T := T.pow_mem t.2 _
    by_contra hu1
    have hne : orderOf u ≠ 1 := fun h => hu1 (orderOf_eq_one_iff.mp h)
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr ha) (even_iff_two_dvd.mpr hrd)
    have hpos : orderOf u ≠ 0 := (orderOf_pos u).ne'
    exact hodd _ (T.pow_mem huT _) r hr hr2 (orderOf_pow_orderOf_div hpos hrd)
  exact le_inSubgroup_pCore hTM hMT hT2 hyT

theorem frattini_ne_bot_of_exists_mul_self_ne_one {P : Subgroup G} (hP : IsPGroup 2 P) {x : G}
    (hx : x ∈ P) (hxx : x * x ≠ 1) : frattini ↥P ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 ↥P) := ⟨hP⟩
  intro h
  have h1 := CFSG.pth_power_mem_frattini_of_isPGroup (R := ↥P) (p := 2) ⟨x, hx⟩
  rw [h, Subgroup.mem_bot] at h1
  apply hxx
  have := congrArg Subtype.val h1
  simpa [pow_two] using this

theorem commute_of_conjSubgroup_le_of_isTI_cyclic {A : Subgroup G} (hcyc : IsCyclic ↥A)
    (hA2 : IsPGroup 2 A) (hTI : IsTI A) (h4 : 4 ≤ Nat.card ↥A) {S : Subgroup G}
    (hS : IsPGroup 2 S) {g h : G} (hg : conjSubgroup g A ≤ S) (hh : conjSubgroup h A ≤ S) :
    ∀ a ∈ conjSubgroup g A, ∀ b ∈ conjSubgroup h A, a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro a ha b hb
  by_cases heq : conjSubgroup g A = conjSubgroup h A
  · rw [← heq] at hb
    have hcycg : IsCyclic ↥(conjSubgroup g A) := by
      let e : ↥A ≃* ↥(conjSubgroup g A) :=
        A.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
      exact isCyclic_of_surjective e.toMonoidHom e.surjective
    exact forall_mul_comm_of_isCyclic hcycg a ha b hb
  · let Δ : Set (Subgroup G) := {C | ∃ k : G, C = conjSubgroup k A ∧ C ≤ S}
    have hΔ := CFSG.ComponentClassification.Asc76X.lemma25 (S := S) (Δ := Δ) hS
      (fun C ⟨k, _, hC⟩ => hC)
      (by
        rintro C ⟨k, rfl, hCS⟩ s hs
        refine ⟨s⁻¹ * k, ?_, ?_⟩
        · unfold CFSG.ComponentClassification.AschbacherTightEmbedding.rightConjugate
          rw [conjSubgroup_mul]; rfl
        · intro x hx
          obtain ⟨y, hy, rfl⟩ := hx
          have := hCS hy
          have h2 : (MulAut.conj s⁻¹).toMonoidHom y = s⁻¹ * y * s := by
            show s⁻¹ * y * s⁻¹⁻¹ = _
            simp
          rw [h2]
          exact S.mul_mem (S.mul_mem (S.inv_mem hs) this) hs)
      (by
        rintro C ⟨k, rfl, -⟩ T ⟨k', rfl, -⟩
        rw [card_conjSubgroup, card_conjSubgroup])
      (by
        rintro C ⟨k, rfl, hCS⟩
        have hC2 : IsPGroup 2 ↥(conjSubgroup k A) := hA2.map (MulAut.conj k).toMonoidHom
        obtain ⟨r, hr⟩ := hcyc.exists_generator
        have hord : orderOf r = Nat.card ↥A := orderOf_eq_card_of_forall_mem_zpowers hr
        have hrr : (r : G) * r ≠ 1 := by
          intro h1
          have : orderOf (r : G) ∣ 2 := by
            apply orderOf_dvd_of_pow_eq_one
            rw [sq]; exact h1
          rw [Subgroup.orderOf_coe, hord] at this
          have := Nat.le_of_dvd (by norm_num) this
          omega
        have hmem : k * (r : G) * k⁻¹ ∈ conjSubgroup k A :=
          ⟨r, r.2, by simp [MulAut.conj_apply]⟩
        refine frattini_ne_bot_of_exists_mul_self_ne_one hC2 hmem ?_
        intro h1
        apply hrr
        have : (r : G) * r = k⁻¹ * ((k * r * k⁻¹) * (k * r * k⁻¹)) * k := by group
        rw [this, h1]; group)
      (by
        rintro C ⟨k, rfl, -⟩ T ⟨k', rfl, -⟩ hne
        have hT : conjSubgroup k' A = conjSubgroup k (conjSubgroup (k⁻¹ * k') A) := by
          rw [← conjSubgroup_mul]; congr 1; group
        rw [hT, ← conjSubgroup_inf]
        rcases hTI (k⁻¹ * k') with h1 | h1
        · rw [h1]; exact Subgroup.map_bot _
        · exfalso
          apply hne
          have hle : A ≤ conjSubgroup (k⁻¹ * k') A := inf_eq_left.mp h1
          have heq' : A = conjSubgroup (k⁻¹ * k') A :=
            Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])
          calc conjSubgroup k A = conjSubgroup k (conjSubgroup (k⁻¹ * k') A) := by rw [← heq']
            _ = conjSubgroup k' A := by rw [← conjSubgroup_mul]; congr 1; group)
    have := hΔ _ ⟨g, rfl, hg⟩ _ ⟨h, rfl, hh⟩ heq
    have h3 : conjSubgroup g A ≤ Subgroup.centralizer (conjSubgroup h A : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp this
    exact (Subgroup.mem_centralizer_iff.mp (h3 ha) b hb).symm

omit [Finite G] in
theorem mem_normalizer_conjSubgroup_iff_conj_mem_normalizer (g y : G) (X : Subgroup G) :
    y ∈ Subgroup.normalizer ((conjSubgroup g X : Subgroup G) : Set G) ↔
      g⁻¹ * y * g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h w
    have h1 := h (g * w * g⁻¹)
    rw [mem_conjSubgroup, mem_conjSubgroup] at h1
    have e1 : g⁻¹ * (g * w * g⁻¹) * g = w := by group
    have e2 : g⁻¹ * (y * (g * w * g⁻¹) * y⁻¹) * g = g⁻¹ * y * g * w * (g⁻¹ * y * g)⁻¹ := by
      group
    rw [e1, e2] at h1
    exact h1
  · intro h z
    have h1 := h (g⁻¹ * z * g)
    rw [mem_conjSubgroup, mem_conjSubgroup]
    have e2 : g⁻¹ * (y * z * y⁻¹) * g = g⁻¹ * y * g * (g⁻¹ * z * g) * (g⁻¹ * y * g)⁻¹ := by
      group
    rw [e2]
    exact h1

omit [Finite G] in
theorem forall_mul_comm_of_mem_iSup {ι : Type*} (T : ι → Subgroup G)
    (h : ∀ i j, ∀ a ∈ T i, ∀ b ∈ T j, a * b = b * a) :
    ∀ a ∈ ⨆ i, T i, ∀ b ∈ ⨆ i, T i, a * b = b * a := by
  have h1 : ∀ j, ∀ b ∈ T j, ∀ a ∈ ⨆ i, T i, a * b = b * a := by
    intro j b hb a ha
    refine Subgroup.iSup_induction T (C := fun a => a * b = b * a) ha ?_ ?_ ?_
    · intro i x hx
      exact h i j x hx b hb
    · simp
    · intro x y hx hy
      calc x * y * b = x * (y * b) := by group
        _ = x * (b * y) := by rw [hy]
        _ = (x * b) * y := by group
        _ = (b * x) * y := by rw [hx]
        _ = b * (x * y) := by group
  intro a ha b hb
  refine Subgroup.iSup_induction T (C := fun b => a * b = b * a) hb ?_ ?_ ?_
  · intro j x hx
    exact h1 j x hx a ha
  · simp
  · intro x y hx hy
    calc a * (x * y) = (a * x) * y := by group
      _ = (x * a) * y := by rw [hx]
      _ = x * (a * y) := by group
      _ = x * (y * a) := by rw [hy]
      _ = (x * y) * a := by group

theorem exists_eq_sq_of_card_eq_four_of_le_cyclic {A K₂ : Subgroup G} (hcyc : IsCyclic ↥A)
    (hA2 : IsPGroup 2 A) (h8 : 8 ≤ Nat.card ↥A) (hK₂ : K₂ ≤ A) (hK₂4 : Nat.card ↥K₂ = 4) :
    ∀ k ∈ K₂, ∃ a ∈ A, k = a ^ 2 := by
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hA2
  have hm3 : 3 ≤ m := by
    by_contra hlt
    have : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨r, hr⟩ := hcyc.exists_generator
  have hord : orderOf (r : G) = 2 ^ m := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hr, hm]
  intro k hk
  have hkA : k ∈ A := hK₂ hk
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hr ⟨k, hkA⟩)
  have hkj : k = (r : G) ^ j := by simpa using (congrArg Subtype.val hj).symm
  have hk4 : k ^ 4 = 1 := by
    have := orderOf_dvd_iff_pow_eq_one.mp (hK₂4 ▸ Subgroup.orderOf_dvd_natCard K₂ hk)
    exact this
  have h1 : (r : G) ^ (j * 4) = 1 := by
    rw [hkj, ← zpow_natCast, ← zpow_mul] at hk4
    simpa using hk4
  have h2 := (orderOf_dvd_iff_zpow_eq_one).mpr h1
  rw [hord] at h2
  have h3 : (8 : ℤ) ∣ j * 4 := by
    have : (8 : ℤ) ∣ 2 ^ m := by
      have : (2 : ℤ) ^ m = 8 * 2 ^ (m - 3) := by
        rw [show (8 : ℤ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega
      rw [this]; exact dvd_mul_right _ _
    exact this.trans (by exact_mod_cast h2)
  obtain ⟨j', hj'⟩ : ∃ j' : ℤ, j = 2 * j' := ⟨j / 2, by omega⟩
  refine ⟨(r : G) ^ j', Subgroup.zpow_mem _ r.2 j', ?_⟩
  rw [hkj, hj', mul_comm, zpow_mul]
  simp

theorem STSetting.weaklyClosedInNormalizer_of_card_four (S : STSetting G K) (R : Sylow 2 K)
    (hcyc : IsCyclic ↥(sylowImg R)) (h8 : 8 ≤ Nat.card ↥(sylowImg R)) {K₂ : Subgroup G}
    (hK₂ : K₂ ≤ sylowImg R) (hK₂4 : Nat.card ↥K₂ = 4) : WeaklyClosedInNormalizer K₂ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple := S.simple
  set A := sylowImg R with hAdef
  set M := Subgroup.normalizer (K : Set G) with hMdef
  have hA2 : IsPGroup 2 A := isPGroup_sylowImg R
  have hcommA : IsCommSubgroup A := forall_mul_comm_of_isCyclic hcyc
  have hNA : Subgroup.normalizer (A : Set G) = M := S.normalizer_sylowImg_eq R hcommA
  have hTI : IsTI A := S.isTI_sylowImg R hcommA
  have hF : generalizedFitting M = pCore 2 M :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore _ 2).mp S.isCharacteristicP
  set Q := inSubgroup (pCore 2) M with hQdef
  obtain ⟨hQ2, hQM, hMQ⟩ := inSubgroup_pCore_two M
  have hAM : A ≤ M := hNA ▸ Subgroup.le_normalizer
  have hAQ : A ≤ Q := le_inSubgroup_pCore hAM (hNA.symm ▸ le_rfl) hA2
  have hK₂ne : K₂ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hK₂4
    omega
  have hK₂2 : IsPGroup 2 K₂ := hA2.to_le hK₂
  have hK₂cyc : IsCyclic ↥K₂ := by
    have := hcyc
    exact Subgroup.isCyclic_of_le hK₂
  have hconjK₂ : ∀ m ∈ M, conjSubgroup m K₂ = K₂ := by
    intro m hm
    have hmA : m ∈ Subgroup.normalizer (A : Set G) := hNA ▸ hm
    have hconjA : conjSubgroup m A = A := conjSubgroup_eq_self_iff.mpr hmA
    have hle : conjSubgroup m K₂ ≤ A := hconjA ▸ Subgroup.map_mono hK₂
    exact eq_of_card_eq_of_le_of_isCyclic hcyc hle hK₂ (by rw [card_conjSubgroup])
  have hMK₂ : M ≤ Subgroup.normalizer (K₂ : Set G) := fun m hm =>
    conjSubgroup_eq_self_iff.mp (hconjK₂ m hm)
  have hNK₂ : Subgroup.normalizer (K₂ : Set G) = M := by
    refine le_antisymm ?_ hMK₂
    by_contra hnot
    exact S.max.2 _ (lt_of_le_of_ne hMK₂ (fun h => hnot (h ▸ le_rfl))) ⟨K₂, hK₂ne, hK₂2, rfl⟩
  have hkey : ∀ g : G, conjSubgroup g K₂ ≤ M → g ∈ M := by
    have hC : ∀ f : G, conjSubgroup f K₂ ≤ M → conjSubgroup f K₂ ≤ Q := by
      intro f hf
      by_cases hfM : f ∈ M
      · rw [hconjK₂ f hfM]; exact hK₂.trans hAQ
      · have hfA : f ∉ Subgroup.normalizer (A : Set G) := fun h' => hfM (hNA ▸ h')
        have hf' : conjSubgroup f K₂ ≤ Subgroup.normalizer (A : Set G) := hNA ▸ hf
        obtain ⟨hB1, -⟩ := conj_le_normalizer_of_card_four_conj_le_normalizer hcyc hA2 hTI h8 hK₂
          hK₂4 hfA hf'
        have hB1' : conjSubgroup f A ≤ M := hNA ▸ hB1
        have hB2 : IsPGroup 2 (conjSubgroup f A) := hA2.map (MulAut.conj f).toMonoidHom
        obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow (G := ↥M)
          (P := (conjSubgroup f A).subgroupOf M)
          (hB2.of_equiv (Subgroup.subgroupOfEquivOfLe hB1').symm)
        set S₀ : Subgroup G := (P : Subgroup M).map M.subtype with hS₀
        have hS₀2 : IsPGroup 2 S₀ := P.isPGroup'.map M.subtype
        have hBS : conjSubgroup f A ≤ S₀ := by
          intro b hb
          exact ⟨⟨b, hB1' hb⟩, hP (Subgroup.mem_subgroupOf.mpr hb), rfl⟩
        have hQS : Q ≤ S₀ := by
          have hnorm : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal (p := 2)
          have hle : CFSG.pCore 2 ↥M ≤ (P : Subgroup M) :=
            (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).le_sylow_of_normal P
          exact Subgroup.map_mono hle
        have hsq : ∀ x ∈ conjSubgroup f A, x ^ 2 ∈ Q := by
          intro x hx
          have hxM : x ∈ M := hB1' hx
          refine sq_mem_pCore_of_commutator_centralizes hF hxM ?_
          intro q hq
          have hqS : q ∈ S₀ := hQS hq
          have hb : q⁻¹ * x * q ∈ conjSubgroup (q⁻¹ * f) A := by
            rw [mem_conjSubgroup] at hx ⊢
            have : (q⁻¹ * f)⁻¹ * (q⁻¹ * x * q) * (q⁻¹ * f) = f⁻¹ * x * f := by group
            rw [this]; exact hx
          have hqf : conjSubgroup (q⁻¹ * f) A ≤ S₀ := by
            intro y hy
            rw [mem_conjSubgroup] at hy
            have h1 : q * y * q⁻¹ ∈ conjSubgroup f A := by
              rw [mem_conjSubgroup]
              have : f⁻¹ * (q * y * q⁻¹) * f = (q⁻¹ * f)⁻¹ * y * (q⁻¹ * f) := by group
              rw [this]; exact hy
            have h2 := hBS h1
            have : y = q⁻¹ * (q * y * q⁻¹) * q := by group
            rw [this]
            exact S₀.mul_mem (S₀.mul_mem (S₀.inv_mem hqS) h2) hqS
          have hcm := commute_of_conjSubgroup_le_of_isTI_cyclic hcyc hA2 hTI (by omega) hS₀2 hBS hqf
          have c1 : x * (q⁻¹ * x * q) = (q⁻¹ * x * q) * x := hcm x hx _ hb
          calc (q⁻¹ * x * q * x⁻¹) * x = q⁻¹ * x * q := by group
            _ = x * (q⁻¹ * x * q * x⁻¹) := by
              calc q⁻¹ * x * q = ((q⁻¹ * x * q) * x) * x⁻¹ := by group
                _ = (x * (q⁻¹ * x * q)) * x⁻¹ := by rw [c1]
                _ = x * (q⁻¹ * x * q * x⁻¹) := by group
        intro y hy
        obtain ⟨k, hk, rfl⟩ := hy
        obtain ⟨a, haA, hka⟩ := exists_eq_sq_of_card_eq_four_of_le_cyclic hcyc hA2 h8 hK₂ hK₂4 k hk
        have hfa : f * a * f⁻¹ ∈ conjSubgroup f A := ⟨a, haA, rfl⟩
        have e : (MulAut.conj f).toMonoidHom k = (f * a * f⁻¹) ^ 2 := by
          rw [hka]
          show f * a ^ 2 * f⁻¹ = (f * a * f⁻¹) ^ 2
          rw [sq, sq]; group
        rw [e]
        exact hsq _ hfa
    let V : Subgroup G := ⨆ f : {f : G // conjSubgroup f K₂ ≤ M}, conjSubgroup (f : G) K₂
    have hVQ : V ≤ Q := iSup_le fun f => hC f f.2
    have hone : conjSubgroup (1 : G) K₂ = K₂ := by ext x; simp [mem_conjSubgroup]
    have hK₂V : K₂ ≤ V := by
      have h1 : conjSubgroup (1 : G) K₂ ≤ M := by rw [hone]; exact hK₂.trans hAM
      calc K₂ = conjSubgroup (1 : G) K₂ := hone.symm
        _ ≤ V := le_iSup (fun f : {f : G // conjSubgroup f K₂ ≤ M} => conjSubgroup (f : G) K₂)
            ⟨1, h1⟩
    have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
      apply forall_mul_comm_of_mem_iSup
      intro f f' a ha b hb
      exact commute_of_conjSubgroup_le_of_isTI_cyclic hK₂cyc hK₂2
        (isTI_of_le_cyclic hcyc hTI hK₂) (by omega) hQ2 (hC f f.2) (hC f' f'.2) a ha b hb
    have hVM : ∀ m ∈ M, conjSubgroup m V ≤ V := by
      intro m hm
      have : conjSubgroup m V = ⨆ f : {f : G // conjSubgroup f K₂ ≤ M},
          conjSubgroup m (conjSubgroup (f : G) K₂) := Subgroup.map_iSup _ _
      rw [this]
      refine iSup_le fun f => ?_
      have hmf : conjSubgroup (m * (f : G)) K₂ ≤ M := by
        rw [conjSubgroup_mul]
        rintro y ⟨z, hz, rfl⟩
        have := f.2 hz
        show m * z * m⁻¹ ∈ M
        exact M.mul_mem (M.mul_mem hm this) (M.inv_mem hm)
      rw [← conjSubgroup_mul]
      exact le_iSup (fun f : {f : G // conjSubgroup f K₂ ≤ M} => conjSubgroup (f : G) K₂)
        ⟨m * f, hmf⟩
    intro g hg
    by_contra hgM
    have hgA : g ∉ Subgroup.normalizer (A : Set G) := fun h' => hgM (hNA ▸ h')
    have hg' : conjSubgroup g K₂ ≤ Subgroup.normalizer (A : Set G) := hNA ▸ hg
    obtain ⟨hB1, hB2⟩ := conj_le_normalizer_of_card_four_conj_le_normalizer hcyc hA2 hTI h8 hK₂
      hK₂4 hgA hg'
    have hgV : conjSubgroup g K₂ ≤ V :=
      le_iSup (fun f : {f : G // conjSubgroup f K₂ ≤ M} => conjSubgroup (f : G) K₂) ⟨g, hg⟩
    obtain ⟨k, hk, hk1⟩ : ∃ k ∈ K₂, k ≠ 1 := by
      by_contra hno
      push Not at hno
      exact hK₂ne (eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hno x hx))
    have hgk : g * k * g⁻¹ ∈ conjSubgroup g A := ⟨k, hK₂ hk, rfl⟩
    have hgk1 : g * k * g⁻¹ ≠ 1 := by
      intro h'
      apply hk1
      have : k = g⁻¹ * (g * k * g⁻¹) * g := by group
      rw [this, h']; group
    have hVN : ∀ y ∈ V, y ∈ Subgroup.normalizer ((conjSubgroup g A : Subgroup G) : Set G) := by
      intro y hy
      have hc := hVcomm y hy (g * k * g⁻¹) (hgV ⟨k, hk, rfl⟩)
      exact centralizer_le_normalizer_of_isTI (isTI_conjSubgroup hTI g) hgk hgk1 hc
    have hVM' : ∀ y ∈ V, g⁻¹ * y * g ∈ M := by
      intro y hy
      have := (mem_normalizer_conjSubgroup_iff_conj_mem_normalizer g y A).mp (hVN y hy)
      exact hNA ▸ this
    have hgV' : conjSubgroup g⁻¹ V ≤ V := by
      have : conjSubgroup g⁻¹ V = ⨆ f : {f : G // conjSubgroup f K₂ ≤ M},
          conjSubgroup g⁻¹ (conjSubgroup (f : G) K₂) := Subgroup.map_iSup _ _
      rw [this]
      refine iSup_le fun f => ?_
      have hmf : conjSubgroup (g⁻¹ * (f : G)) K₂ ≤ M := by
        rw [conjSubgroup_mul]
        rintro y ⟨z, hz, rfl⟩
        have hzV : z ∈ V :=
          le_iSup (fun f : {f : G // conjSubgroup f K₂ ≤ M} => conjSubgroup (f : G) K₂) f hz
        have := hVM' z hzV
        show g⁻¹ * z * g⁻¹⁻¹ ∈ M
        simpa using this
      rw [← conjSubgroup_mul]
      exact le_iSup (fun f : {f : G // conjSubgroup f K₂ ≤ M} => conjSubgroup (f : G) K₂)
        ⟨g⁻¹ * f, hmf⟩
    have hcardV : conjSubgroup g⁻¹ V = V :=
      Subgroup.eq_of_le_of_card_ge hgV' (by rw [card_conjSubgroup])
    have hgNV : g ∈ Subgroup.normalizer (V : Set G) := by
      have := conjSubgroup_eq_self_iff.mp hcardV
      simpa using inv_mem this
    have hMV : M ≤ Subgroup.normalizer (V : Set G) := by
      intro m hm
      refine conjSubgroup_eq_self_iff.mp ?_
      exact Subgroup.eq_of_le_of_card_ge (hVM m hm) (by rw [card_conjSubgroup])
    have hlt : M < Subgroup.normalizer (V : Set G) :=
      lt_of_le_of_ne hMV (fun h' => hgM (by rw [h']; exact hgNV))
    have hVne : V ≠ ⊥ := fun h' => hK₂ne (eq_bot_iff.mpr (h' ▸ hK₂V))
    exact S.max.2 _ hlt ⟨V, hVne, hQ2.to_le hVQ, rfl⟩
  intro h hh
  have hh' : conjSubgroup h K₂ ≤ M := hNK₂ ▸ hh
  exact conjSubgroup_eq_self_iff.mpr (hNK₂ ▸ hkey h hh')

theorem STSetting.dihedral_of_cyclic_ge_eight (hL25 : Asc76Lemma25) (S : STSetting G K)
    (R : Sylow 2 K) (hcyc : IsCyclic ↥(sylowImg R)) (h8 : 8 ≤ Nat.card ↥(sylowImg R)) :
    HasDihedralSylowTwo G ∨ HasSemidihedralSylowTwo G := by
  have := S.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (isPGroup_sylowImg R)
  have hm3 : 3 ≤ m := by
    by_contra hlt
    have : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨r, hr⟩ := hcyc.exists_generator
  have hord : orderOf r = 2 ^ m := by rw [orderOf_eq_card_of_forall_mem_zpowers hr, hm]
  set x₀ : ↥(sylowImg R) := r ^ 2 ^ (m - 2) with hx₀
  have hx₀ord : orderOf x₀ = 4 := by
    rw [hx₀, orderOf_pow' _ (by positivity), hord]
    have : 2 ^ m = 2 ^ (m - 2) * 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    rw [this, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
  set x : G := (x₀ : G) with hx
  have hx4 : orderOf x = 4 := by rw [hx, Subgroup.orderOf_coe, hx₀ord]
  have hK₂ : Subgroup.zpowers x ≤ sylowImg R := (Subgroup.zpowers_le).mpr x₀.2
  have hK₂4 : Nat.card ↥(Subgroup.zpowers x) = 4 := by rw [Nat.card_zpowers, hx4]
  have hW := S.weaklyClosedInNormalizer_of_card_four R hcyc h8 hK₂ hK₂4
  have hz1 : x ^ 2 ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hx4] at this
    omega
  have hX : (Subgroup.normalClosure {x ^ 2} : Subgroup G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.normalClosure {x ^ 2} : Subgroup G) with h | h
    · exfalso
      have hmem : x ^ 2 ∈ (Subgroup.normalClosure {x ^ 2} : Subgroup G) :=
        Subgroup.subset_normalClosure (Set.mem_singleton _)
      rw [h, Subgroup.mem_bot] at hmem
      exact hz1 hmem
    · exact h
  rcases hL25 G x hx4 hW with hZ | hD | hSD
  · exact absurd hZ (not_inZStar_of_simple S.nonab hx4)
  · exact Or.inl
      (hasDihedralSylowTwo_transfer ((MulEquiv.subgroupCongr hX).trans Subgroup.topEquiv) hD)
  · exact Or.inr
      (hasSemidihedralSylowTwo_transfer ((MulEquiv.subgroupCongr hX).trans Subgroup.topEquiv) hSD)

end CFSG.CGT.PushingUpLit.SolKAb
