module

public import CFSG.HardMathSupport.Timmesfeld.LinearRank.LinCover
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015SU6
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Census.Witness46

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB TauCeti
  CFSG.HardMathSupport.Timmesfeld.LinearRank

namespace I1015

theorem exists_three_quotient {Kg : Type} [Group Kg] [Finite Kg] (hperf : Group.IsPerfect Kg)
    {X : Type} [Group X] (β₀ : Kg →* X) (hβ₀ : Function.Surjective β₀)
    (hker : β₀.ker = Subgroup.center Kg) :
    ∃ (Q : Subgroup Kg) (_ : Q.Normal) (β : Kg ⧸ Q →* X), ¬ 3 ∣ Nat.card Q ∧ Q ≤ β₀.ker ∧
      (∀ g, β (QuotientGroup.mk g) = β₀ g) ∧ Function.Surjective β ∧
      β.ker ≤ Subgroup.center (Kg ⧸ Q) ∧ IsPGroup 3 β.ker ∧ Group.IsPerfect (Kg ⧸ Q) := by
  have hr : Nat.Prime 3 := Nat.prime_three
  set Q := centerPPrime Kg 3 with hQ
  have hQker : Q ≤ β₀.ker := by
    rw [hker]
    exact centerPPrime_le_center Kg 3
  let β : Kg ⧸ Q →* X := QuotientGroup.lift Q β₀ hQker
  have hβmk : ∀ g : Kg, β (QuotientGroup.mk g) = β₀ g := fun g => rfl
  have hβs : Function.Surjective β := by
    intro x
    obtain ⟨g, rfl⟩ := hβ₀ x
    exact ⟨QuotientGroup.mk g, rfl⟩
  have hperf₁ : Group.IsPerfect (Kg ⧸ Q) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' Q) (QuotientGroup.mk'_surjective Q)
  have hgc : ∀ x : Kg ⧸ Q, x ∈ β.ker → ∃ g : Kg, QuotientGroup.mk g = x ∧ g ∈ Subgroup.center Kg := by
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    refine ⟨g, rfl, ?_⟩
    rw [← hker]
    exact (hβmk g).symm.trans (MonoidHom.mem_ker.mp hx)
  have hβc : β.ker ≤ Subgroup.center (Kg ⧸ Q) := by
    intro x hx
    obtain ⟨g, rfl, hg⟩ := hgc x hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hg g']
  have hβp : IsPGroup 3 β.ker := by
    rintro ⟨x, hx⟩
    obtain ⟨g, rfl, hg⟩ := hgc x hx
    set a := (orderOf g).factorization 3 with ha
    have hdvd : 3 ^ a ∣ orderOf g := Nat.ordProj_dvd _ 3
    have hord0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
    have hordg : orderOf (g ^ (3 ^ a)) = orderOf g / 3 ^ a :=
      orderOf_pow_of_dvd (pow_ne_zero _ hr.ne_zero) hdvd
    have hcop : Nat.Coprime 3 (orderOf g / 3 ^ a) := Nat.coprime_ordCompl hr hord0
    have hmem : g ^ (3 ^ a) ∈ Q := ⟨Subgroup.pow_mem _ hg _, by rw [hordg]; exact hcop⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    change (QuotientGroup.mk g : Kg ⧸ Q) ^ (3 ^ a) = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hmem
  exact ⟨Q, inferInstance, β, not_dvd_card_centerPPrime Kg hr, hQker, hβmk, hβs, hβc, hβp, hperf₁⟩

theorem stated_su6_of_isU6two {S : Type} [Group S] (h : catalogIs S S9.isU6two) :
    ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀), Nat.card K₀ = (2 ^ 1) ^ 2 ∧
      Nonempty (S ≃* StatedProj (StatedSU 6 (2 ^ 1) K₀)) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex h
  cases d with
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | _ | _ | r
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
        (hP.trans (by norm_num))
      have hm := lieModel_twistedA' 5 q hv e
      rw [h1, h2] at hm
      obtain ⟨-, K₀, _, _, hK, ⟨e'⟩⟩ := hm.statedClassicalModel (by decide)
      exact ⟨K₀, inferInstance, inferInstance, hK, ⟨e'⟩⟩
    · exact hP.elim
  | _ => exact hP.elim

section Four

variable {G : Type} [Group G] [Finite G]

theorem four_u6two (hGA : GriessAllModelsStatement) {K : Subgroup G}
    (hK : CFSG.Open.IsQuasisimple ↥K) (h : catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isU6two) :
    ∃ F T : Subgroup G, F ≤ K ∧ IsElemAbelian 3 F ∧ T ≤ K ∧ IsPGroup 2 T ∧ T ≠ ⊥ ∧
      F ≤ Subgroup.normalizer (T : Set G) ∧
      3 ^ 3 * Nat.card ↥(F ⊓ Subgroup.centralizer (K : Set G)) ≤ Nat.card F := by
  obtain ⟨K₀, _, _, hK₀, ⟨e⟩⟩ := stated_su6_of_isU6two h
  have h3 : 3 ∣ 2 ^ 1 + 1 := by norm_num
  set β₀ : ↥K →* StatedProj (StatedSU 6 (2 ^ 1) K₀) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K)) with hβ₀
  have hker₀ : β₀.ker = Subgroup.center ↥K := by
    rw [hβ₀, MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective]
    exact QuotientGroup.ker_mk' _
  have hβ₀s : Function.Surjective β₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨Q, hQn, β, hQ3, hQker, hβmk, hβs, hβc, hβp, hperf⟩ :=
    exists_three_quotient ⟨hK.1⟩ β₀ hβ₀s hker₀
  obtain ⟨Eb, s, hEb, hEbc, hs2, hβs1, hc⟩ := exists_Ebar_s_of_cover hGA h3 hK₀ hperf β hβs hβc hβp
  have hs1 : s ≠ 1 := fun h => hβs1 (by rw [h, map_one])
  set π : ↥K →* ↥K ⧸ Q := QuotientGroup.mk' Q with hπ
  have hπker : π.ker = Q := QuotientGroup.ker_mk' Q
  obtain ⟨F, T, W, hFW, hFK, hFe, hFc, hWmap, hWinj, hTK, hT2, hFN, t, htT, hπt⟩ :=
    exists_two_local_lift_subgroup π (QuotientGroup.mk'_surjective _) (by rw [hπker]; exact hQ3) hEb
      (isPGroup_zpowers_of_pow_eq_one hs2) (by rwa [Ne, Subgroup.zpowers_eq_bot])
      (fun e he => mem_normalizer_zpowers_of_commute (hc e he))
  refine ⟨F, T, hFK, hFe, hTK, hT2, ?_, hFN, ?_⟩
  · intro hT
    apply hπt
    rw [hT, Subgroup.mem_bot] at htT
    have : t = 1 := Subtype.ext htT
    rw [this, map_one]
  · set Wc : Subgroup ↥K := W ⊓ Subgroup.center ↥K with hWc
    have hFC : F ⊓ Subgroup.centralizer (K : Set G) ≤ Wc.map K.subtype := by
      rintro x ⟨hxF, hxC⟩
      rw [hFW] at hxF
      obtain ⟨w, hw, rfl⟩ := hxF
      have hwz : w ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro k
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.1 hxC (k : G) k.2
      exact ⟨w, ⟨hw, hwz⟩, rfl⟩
    have hWcβ : Wc.map π ≤ β.ker := by
      rintro _ ⟨w, ⟨hw, hwz⟩, rfl⟩
      rw [MonoidHom.mem_ker]
      change β (QuotientGroup.mk w) = 1
      rw [hβmk, ← MonoidHom.mem_ker, hker₀]
      exact hwz
    have hinjc : Function.Injective (π.comp Wc.subtype) := by
      intro a b hab
      have h' : (⟨a.1, a.2.1⟩ : W) = ⟨b.1, b.2.1⟩ := hWinj hab
      have h'' := congrArg Subtype.val h'
      exact Subtype.ext h''
    have h1 : Nat.card ↥(F ⊓ Subgroup.centralizer (K : Set G)) ≤ Nat.card ↥(Wc.map K.subtype) :=
      Subgroup.card_le_of_le hFC
    have h2 : Nat.card ↥(Wc.map K.subtype) = Nat.card ↥Wc :=
      Subgroup.card_map_of_injective K.subtype_injective
    have h3' : Nat.card ↥Wc = Nat.card ↥(Wc.map π) := card_eq_of_injective_comp_subtype π hinjc
    have h4 : Nat.card ↥(Wc.map π) ≤ Nat.card ↥β.ker := Subgroup.card_le_of_le hWcβ
    calc 3 ^ 3 * Nat.card ↥(F ⊓ Subgroup.centralizer (K : Set G))
        ≤ 3 ^ 3 * Nat.card ↥β.ker := Nat.mul_le_mul_left _ (by omega)
      _ = Nat.card F := by rw [hFc, hEbc]; norm_num

end Four

end I1015

end CFSG.LocalAnalysis.GLTheoremA.CatB
