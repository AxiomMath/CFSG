module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineWLinear
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineOddInnWSmall
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveSmall
public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Small
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceAltSeven
import CFSG.Quasithin.Background.Harris.OrdinaryProofs.CoverSU3
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexSmall

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.FieldIndexW

open Matrix CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock Subgroup Equiv
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (flagStabilizer)
open CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus (IsWBlock)
open scoped commutatorElement

section Normal

variable {Q : Type} [Group Q] [Finite Q]

theorem mem_of_mul_self_eq_one {T : Subgroup Q} [T.Normal] (hT : ¬ 2 ∣ T.index) {z : Q}
    (hz : z * z = 1) : z ∈ T := by
  have h1 : orderOf (QuotientGroup.mk' T z) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, sq, hz, map_one])
  have h2 : orderOf (QuotientGroup.mk' T z) ∣ T.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (QuotientGroup.mk' T z) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact h
    · exact absurd (h ▸ h2) hT
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

open CFSG.Quasithin.Background.Harris in
theorem oddInnW_of_normal (T : Subgroup Q) [T.Normal]
    (hT : T = ⊥ ∨ Nonempty (↥T ≃* Perm (Fin 3))) (hodd : ¬ 2 ∣ T.index)
    (hab : ∀ a b : Q ⧸ T, a * b = b * a) : OddInnW Q := by
  classical
  set 𝒢 := {S : Subgroup Q | IsSubnormal S ⊤ ∧ (IsComponentOf S ⊤ ∨ IsSymThreeOrSUThreeTwo ↥S)}
  have hT6 : Nat.card T ∣ 6 := by
    rcases hT with h | he
    · rw [h, Subgroup.card_bot]
      exact one_dvd _
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      decide
  haveI : Group.IsSolvable T :=
    ToralReduce.isSolvable_of_card_dvd_seventyTwo (hT6.trans (by norm_num))
  haveI : Group.IsSolvable (Q ⧸ T) := isSolvable_of_comm hab
  haveI : Group.IsSolvable Q := solvable_of_ker_le_range T.subtype (QuotientGroup.mk' T) (by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  have hgen : ∀ S ∈ 𝒢, S ≤ T := by
    rintro S ⟨-, hc | hs⟩
    · exfalso
      obtain ⟨-, -, hperf, hsimp⟩ := hc
      haveI : Group.IsPerfect S := Group.isPerfect_def.mpr hperf
      haveI : Nontrivial S := (QuotientGroup.mk'_surjective (Subgroup.center S)).nontrivial
      exact Group.IsPerfect.not_isSolvable (G := S) (subgroup_solvable_of_solvable S)
    · rcases hs with he | ⟨K, _, _, hK, ⟨e⟩⟩
      · obtain ⟨e⟩ := he
        obtain ⟨x, t, -, -, -, htt, hinv, hw⟩ := exists_gens_of_mulEquiv_perm_three e
        have htT : t ∈ T := mem_of_mul_self_eq_one hodd htt
        have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
        have htxT : t * x ∈ T := mem_of_mul_self_eq_one hodd (by
          calc t * x * (t * x) = (t * x * t⁻¹) * x := by rw [ht']; group
            _ = 1 := by rw [hinv, inv_mul_cancel])
        have hxT : x ∈ T := by
          have := T.mul_mem (T.inv_mem htT) htxT
          rwa [inv_mul_cancel_left] at this
        intro y hy
        obtain ⟨i, j, rfl⟩ := hw y hy
        exact T.mul_mem (T.pow_mem hxT j) (T.pow_mem htT i)
      · exfalso
        have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
        have h216 := OrdinaryProofs.card_statedSU_three_two_of_card_four hK'
        have h216' : Nat.card S = 216 := by
          rw [Nat.card_congr e.toEquiv]
          simpa using h216
        have hmul := Subgroup.card_mul_index (T.subgroupOf S)
        have hidx : (T.subgroupOf S).index ∣ T.index := Subgroup.relIndex_dvd_index_of_normal T S
        have hcard : Nat.card (T.subgroupOf S) ∣ 6 := by
          refine Dvd.dvd.trans ?_ hT6
          rw [← Subgroup.card_map_of_injective S.subtype_injective, Subgroup.subgroupOf_map_subtype]
          exact Subgroup.card_dvd_of_le inf_le_left
        have hr : Odd (T.subgroupOf S).index :=
          Odd.of_dvd_nat (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)) hidx
        have ha6 : Nat.card (T.subgroupOf S) ≤ 6 := Nat.le_of_dvd (by norm_num) hcard
        rw [h216'] at hmul
        obtain ⟨k, hk⟩ := hr
        rw [hk] at hmul
        interval_cases (Nat.card (T.subgroupOf S)) <;> omega
  have hWT : wSup Q ≤ T := iSup₂_le hgen
  rcases hT with h | he
  · intro α _
    refine ⟨1, one_mem _, fun x hx => ?_⟩
    rw [h] at hWT
    rw [Subgroup.mem_bot.mp (hWT hx)]
    simp
  · obtain ⟨e⟩ := he
    have hsub : IsSubnormal T ⊤ :=
      IsSubnormal.step le_top ((inferInstance : T.Normal).subgroupOf ⊤) (IsSubnormal.refl ⊤)
    have hW : wSup Q = T := le_antisymm hWT
      (le_iSup₂ (f := fun (S : Subgroup Q) (_ : S ∈ 𝒢) => S) T ⟨hsub, Or.inr (Or.inl ⟨e⟩)⟩)
    exact oddInnW_of_wSup_eq hW e

end Normal

open CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus in
theorem oddInnW_quotient_of_card_dvd {J : Type} [Group J] [Finite J] {Z : Subgroup J}
    [Z.Normal] (hZ : Z ≤ center J) (hZo : Odd (Nat.card Z)) (h96 : Nat.card (J ⧸ Z) ∣ 96) :
    OddInnW (J ⧸ CFSG.pCore 2 J) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : J →* J ⧸ Z := QuotientGroup.mk' Z with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hπker : π.ker = Z := QuotientGroup.ker_mk' Z
  set q := QuotientGroup.mk' (CFSG.pCore 2 J) with hq
  have hcen : Z.map q ≤ center (J ⧸ CFSG.pCore 2 J) := by
    rintro - ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 J) w
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hZ hz) x]
  have hsupq : ∀ x ∈ Z ⊔ CFSG.pCore 2 J, q x ∈ Z.map q := by
    intro x hx
    have hqbot : (CFSG.pCore 2 J).map q = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hq, QuotientGroup.ker_mk']
    have hxq : q x ∈ (Z ⊔ CFSG.pCore 2 J).map q := Subgroup.mem_map_of_mem _ hx
    rwa [Subgroup.map_sup, hqbot, sup_bot_eq] at hxq
  have hidx3 : ∀ T : Sylow 2 (J ⧸ Z), T.index ∣ 3 := by
    intro T
    have hdvd : T.index ∣ 96 := (Subgroup.index_dvd_card _).trans h96
    rw [show (96 : ℕ) = 2 ^ 5 * 3 from by norm_num] at hdvd
    have hcop : Nat.Coprime T.index (2 ^ 5) :=
      Nat.Coprime.pow_right 5
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr T.not_dvd_index).symm
    exact hcop.dvd_of_dvd_mul_left hdvd
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 (J ⧸ Z)) := inferInstance
  by_cases hT₀ : T₀.Normal
  ·
    set M : Subgroup J := (T₀ : Subgroup (J ⧸ Z)).comap π with hM
    have hMn : M.Normal := hT₀.comap π
    have hZM : Z ≤ M := by
      intro z hz
      rw [hM, Subgroup.mem_comap, show π z = 1 from by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hz]
      exact (T₀ : Subgroup (J ⧸ Z)).one_mem
    have hquot : IsPGroup 2 (↥M ⧸ Z.subgroupOf M) :=
      isPGroup_quotient_subgroupOf_comap hπs hπker.symm T₀.isPGroup'
    have hMD : M ≤ Z ⊔ CFSG.pCore 2 J :=
      le_sup_pCore_two_of_central_odd_quotient_two hMn hZM hZ hZo hquot
    have hpcM : CFSG.pCore 2 J ≤ M := by
      haveI hn : ((CFSG.pCore 2 J).map π).Normal :=
        (CFSG.pCore_normal (p := 2) (G := J)).map π hπs
      have hle : (CFSG.pCore 2 J).map π ≤ (T₀ : Subgroup (J ⧸ Z)) :=
        IsPGroup.le_sylow_of_normal ((CFSG.pCore_isPGroup (p := 2) (G := J)).map π) T₀
      intro x hx
      rw [hM, Subgroup.mem_comap]
      exact hle (Subgroup.mem_map_of_mem π hx)
    have hMi : M.index = (T₀ : Subgroup (J ⧸ Z)).index := by
      rw [hM]
      exact Subgroup.index_comap_of_surjective (T₀ : Subgroup (J ⧸ Z)) hπs
    haveI := hMn
    let f : J ⧸ CFSG.pCore 2 J →* J ⧸ M := QuotientGroup.map _ _ (MonoidHom.id J) hpcM
    have hfker : f.ker ≤ center (J ⧸ CFSG.pCore 2 J) := by
      intro y hy
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 J) y
      have hx : x ∈ M := by
        rw [MonoidHom.mem_ker] at hy
        exact (QuotientGroup.eq_one_iff x).mp hy
      exact hcen (hsupq x (hMD hx))
    haveI : IsCyclic (J ⧸ M) := by
      have h3 : Nat.card (J ⧸ M) ∣ 3 := by
        rw [← Subgroup.index_eq_card, hMi]
        exact hidx3 T₀
      rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
      · haveI : Subsingleton (J ⧸ M) := (Nat.card_eq_one_iff_unique.mp h).1
        exact isCyclic_of_subsingleton
      · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        exact isCyclic_of_prime_card h
    have hcomm := commutative_of_cyclic_center_quotient f hfker
    refine oddInnW_of_normal ⊥ (Or.inl rfl) ?_ fun a b => ?_
    ·
      rw [Subgroup.index_bot]
      have hrel : (CFSG.pCore 2 J).relIndex M ∣ Nat.card Z := by
        have h1 : (CFSG.pCore 2 J).relIndex M ∣
            (CFSG.pCore 2 J).relIndex (Z ⊔ CFSG.pCore 2 J) :=
          ⟨M.relIndex (Z ⊔ CFSG.pCore 2 J),
            (Subgroup.relIndex_mul_relIndex (CFSG.pCore 2 J) M (Z ⊔ CFSG.pCore 2 J) hpcM
              hMD).symm⟩
        refine h1.trans ?_
        rw [Subgroup.relIndex_sup_right]
        exact Subgroup.index_dvd_card (Subgroup.subgroupOf (CFSG.pCore 2 J) Z)
      have heq : Nat.card (J ⧸ CFSG.pCore 2 J) = (CFSG.pCore 2 J).relIndex M * M.index :=
        ((Subgroup.index_eq_card _).symm).trans (Subgroup.relIndex_mul_index hpcM).symm
      rw [heq]
      exact (Odd.mul (Odd.of_dvd_nat hZo hrel)
        (Odd.of_dvd_nat ⟨1, by norm_num⟩ (hMi ▸ hidx3 T₀))).not_two_dvd_nat
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (⊥ : Subgroup (J ⧸ CFSG.pCore 2 J)) a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (⊥ : Subgroup (J ⧸ CFSG.pCore 2 J)) b
      rw [← map_mul, ← map_mul, hcomm x y]
  ·
    have hcard : Nat.card (Sylow 2 (J ⧸ Z)) = 3 := by
      have hdvd : Nat.card (Sylow 2 (J ⧸ Z)) ∣ 3 :=
        (Sylow.card_dvd_index T₀).trans (hidx3 T₀)
      have hne : Nat.card (Sylow 2 (J ⧸ Z)) ≠ 1 := by
        intro h1
        have h2 : (Subgroup.normalizer (T₀ : Set (J ⧸ Z))).index = 1 := by
          rw [← Sylow.card_eq_index_normalizer T₀, h1]
        exact hT₀ (Subgroup.normalizer_eq_top_iff.mp (Subgroup.index_eq_one.mp h2))
      rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h | h
      · exact absurd h hne
      · exact h
    have hidxT : ∀ T : Sylow 2 (J ⧸ Z), T.index = 3 := by
      intro T
      rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three T.index (hidx3 T) with h | h
      · exfalso
        have h1 : Nat.card (Sylow 2 (J ⧸ Z)) ∣ 1 := h ▸ Sylow.card_dvd_index T
        rw [Nat.dvd_one] at h1
        omega
      · exact h
    have hnorm : ∀ T : Sylow 2 (J ⧸ Z),
        Subgroup.normalizer (T : Set (J ⧸ Z)) = (T : Subgroup (J ⧸ Z)) := by
      intro T
      have h1 : (Subgroup.normalizer (T : Set (J ⧸ Z))).index = 3 := by
        rw [← Sylow.card_eq_index_normalizer T, hcard]
      have h2 : T.relIndex (Subgroup.normalizer (T : Set (J ⧸ Z))) = 1 := by
        have h3 : T.relIndex (Subgroup.normalizer (T : Set (J ⧸ Z))) *
            (Subgroup.normalizer (T : Set (J ⧸ Z))).index = T.index :=
          Subgroup.relIndex_mul_index Subgroup.le_normalizer
        rw [h1, hidxT T] at h3
        omega
      exact le_antisymm (Subgroup.relIndex_eq_one.mp h2) Subgroup.le_normalizer
    obtain ⟨φ, hφs, hφ2, hφN⟩ := exists_surjective_perm_fin_three_of_sylow hcard hnorm
    have hpc_le : CFSG.pCore 2 J ≤ (φ.comp π).ker := by
      have hle : (CFSG.pCore 2 J).map π ≤ φ.ker := by
        haveI : ((CFSG.pCore 2 J).map π).Normal :=
          (CFSG.pCore_normal (p := 2) (G := J)).map π hπs
        exact hφN _ inferInstance ((CFSG.pCore_isPGroup (p := 2) (G := J)).map π)
      intro x hx
      rw [MonoidHom.mem_ker]
      exact hle (Subgroup.mem_map_of_mem π hx)
    let f : J ⧸ CFSG.pCore 2 J →* Perm (Fin 3) :=
      QuotientGroup.lift (CFSG.pCore 2 J) (φ.comp π) hpc_le
    have hfs : Function.Surjective f := by
      intro y
      obtain ⟨j, hj⟩ := hφs.comp hπs y
      exact ⟨QuotientGroup.mk j, by
        rw [show f (QuotientGroup.mk j) = (φ.comp π) j from QuotientGroup.lift_mk _ _ j]
        exact hj⟩
    have hMle : (φ.ker).comap π ≤ Z ⊔ CFSG.pCore 2 J := by
      have hMn : ((φ.ker).comap π).Normal := (MonoidHom.normal_ker φ).comap π
      have hZM : Z ≤ (φ.ker).comap π := by
        intro z hz
        rw [Subgroup.mem_comap, MonoidHom.mem_ker, show π z = 1 from by
          rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hz, map_one]
      exact le_sup_pCore_two_of_central_odd_quotient_two hMn hZM hZ hZo
        (isPGroup_quotient_subgroupOf_comap hπs hπker.symm hφ2)
    have hfker : f.ker ≤ Z.map q := by
      intro y hy
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 J) y
      rw [MonoidHom.mem_ker] at hy
      have hx1 : (φ.comp π) x = 1 := by
        rw [← QuotientGroup.lift_mk (CFSG.pCore 2 J) hpc_le x]
        exact hy
      exact hsupq x (hMle (by rw [Subgroup.mem_comap, MonoidHom.mem_ker]; exact hx1))
    have hfodd : Odd (Nat.card f.ker) :=
      Odd.of_dvd_nat hZo ((Subgroup.card_dvd_of_le hfker).trans (Subgroup.card_map_dvd Z _))
    have hfc : ∀ k ∈ f.ker, ∀ y, k * y = y * k := fun k hk y =>
      (Subgroup.mem_center_iff.mp (hcen (hfker hk)) y).symm
    obtain ⟨T, hTn, ⟨eT⟩, hTi⟩ := SymThreeCentralExt.exists_normal_symThree f hfs hfc hfodd
    haveI := hTn
    have hlift : ∀ τ : Perm (Fin 3), τ ^ 2 = 1 → ∃ t ∈ T, f t = τ := by
      intro τ hτ
      obtain ⟨t, ht2, hft⟩ := SymThreeCentralExt.exists_involution_lift f hfs hfodd hτ
      exact ⟨t, mem_of_mul_self_eq_one hTi (by rw [← sq, ht2]), hft⟩
    have hall : ∀ σ : Perm (Fin 3), ∃ t ∈ T, f t = σ := by
      obtain ⟨a, ha, hfa⟩ := hlift (swap 0 1) (by decide)
      obtain ⟨b, hb, hfb⟩ := hlift (swap 1 2) (by decide)
      have hcases : ∀ σ : Perm (Fin 3), σ = 1 ∨ σ = swap 0 1 ∨ σ = swap 1 2 ∨
          σ = swap 0 1 * swap 1 2 ∨ σ = swap 1 2 * swap 0 1 ∨
          σ = swap 0 1 * swap 1 2 * swap 0 1 := by decide
      intro σ
      rcases hcases σ with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, T.one_mem, map_one f⟩
      · exact ⟨a, ha, hfa⟩
      · exact ⟨b, hb, hfb⟩
      · exact ⟨a * b, T.mul_mem ha hb, by rw [map_mul, hfa, hfb]⟩
      · exact ⟨b * a, T.mul_mem hb ha, by rw [map_mul, hfa, hfb]⟩
      · exact ⟨a * b * a, T.mul_mem (T.mul_mem ha hb) ha, by rw [map_mul, map_mul, hfa, hfb]⟩
    have hdec : ∀ x : J ⧸ CFSG.pCore 2 J, ∃ z ∈ f.ker,
        QuotientGroup.mk' T x = QuotientGroup.mk' T z := by
      intro x
      obtain ⟨t, ht, hft⟩ := hall (f x)
      refine ⟨t⁻¹ * x, by rw [MonoidHom.mem_ker, map_mul, map_inv, hft, inv_mul_cancel], ?_⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have : x⁻¹ * (t⁻¹ * x) = (x⁻¹ * t * x)⁻¹ := by group
      rw [this]
      exact T.inv_mem (by simpa [mul_assoc] using hTn.conj_mem t ht x⁻¹)
    refine oddInnW_of_normal T (Or.inr ⟨eT⟩) hTi fun a b => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective T a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective T b
    obtain ⟨z, hz, hxz⟩ := hdec x
    obtain ⟨z', -, hyz⟩ := hdec y
    rw [hxz, hyz, ← map_mul, ← map_mul, hfc z hz z']

theorem oddInnW_of_overgroupOrder96 {X : Type} [Group X] [Finite X] {L J : Subgroup X}
    (hCP : CompParab L J)
    (hord : CFSG.HardMathSupport.Curtis.Proving.OvergroupOrder96 (↥L ⧸ center ↥L)) :
    OddInnW (↥J ⧸ CFSG.pCore 2 ↥J) := by
  classical
  obtain ⟨hJL, T, hT, hTN⟩ := hCP.parab
  have hTJ : T ≤ J := fun x hx => hTN ⟨hT.1 hx, Subgroup.le_normalizer hx⟩
  have hLperf : commutator ↥L = ⊤ := hCP.comp.2.2.1
  set πL : ↥L →* ↥L ⧸ center ↥L := QuotientGroup.mk' (center ↥L) with hπL
  have hπLs : Function.Surjective πL := QuotientGroup.mk'_surjective _
  set Jb : Subgroup ↥L := J.subgroupOf L with hJb
  have hJbne : Jb.map πL ≠ ⊤ := by
    intro htop
    apply hCP.ne_top
    have hJbtop : Jb = ⊤ := by
      refine CFSG.HardMathSupport.Curtis.Proving.top_of_mul_central_of_perfect
        (Subgroup.center ↥L) Jb le_rfl hLperf ?_
      intro g
      have hg : πL g ∈ Jb.map πL := htop ▸ Subgroup.mem_top _
      obtain ⟨h', hh', he⟩ := Subgroup.mem_map.1 hg
      exact ⟨h', hh', h'⁻¹ * g, QuotientGroup.eq.1 he, (mul_inv_cancel_left h' g).symm⟩
    rw [hJb, Subgroup.subgroupOf_eq_top] at hJbtop
    exact le_antisymm hJL hJbtop
  have hT₀ : CFSG.QuasithinUnique.IsSylowTwoOf ((T.subgroupOf L).map πL) ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective
      (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hT) πL hπLs
  have hT₀J : (T.subgroupOf L).map πL ≤ Jb.map πL := Subgroup.map_mono (fun x hx => hTJ hx)
  have h96 : Nat.card (Jb.map πL) ∣ 96 := hord _ _ hT₀ hT₀J hJbne
  have hZc : (Subgroup.center ↥L).comap (Subgroup.inclusion hJL) ≤ center ↥J := by
    intro x hx
    rw [Subgroup.mem_comap] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    refine Subgroup.inclusion_injective hJL ?_
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hx (Subgroup.inclusion hJL y)
  have hZo : Odd (Nat.card ((Subgroup.center ↥L).comap (Subgroup.inclusion hJL))) := by
    refine Odd.of_dvd_nat hCP.odd ?_
    have hcard : Nat.card ↥(Subgroup.map (Subgroup.inclusion hJL)
        ((Subgroup.center ↥L).comap (Subgroup.inclusion hJL))) =
        Nat.card ↥((Subgroup.center ↥L).comap (Subgroup.inclusion hJL)) :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hJL)
    rw [← hcard]
    exact Subgroup.card_dvd_of_le (by rintro - ⟨z, hz, rfl⟩; exact hz)
  have h96' : Nat.card (↥J ⧸ (Subgroup.center ↥L).comap (Subgroup.inclusion hJL)) ∣ 96 := by
    set g : ↥J →* ↥L ⧸ center ↥L := πL.comp (Subgroup.inclusion hJL) with hg
    have hgker : g.ker = (Subgroup.center ↥L).comap (Subgroup.inclusion hJL) := by
      ext x
      rw [MonoidHom.mem_ker, hg, MonoidHom.comp_apply, Subgroup.mem_comap, hπL,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hgrange : g.range = Jb.map πL := by
      rw [hg, MonoidHom.range_comp, Subgroup.inclusion_range]
    have e : ↥J ⧸ (Subgroup.center ↥L).comap (Subgroup.inclusion hJL) ≃* ↥(Jb.map πL) :=
      (QuotientGroup.quotientMulEquivOfEq hgker.symm).trans
        ((QuotientGroup.quotientKerEquivRange g).trans (MulEquiv.subgroupCongr hgrange))
    rw [show Nat.card (↥J ⧸ (Subgroup.center ↥L).comap (Subgroup.inclusion hJL))
        = Nat.card ↥(Jb.map πL) from Nat.card_congr e.toEquiv]
    exact h96
  exact oddInnW_quotient_of_card_dvd hZc hZo h96'

theorem leviInnAtW_alt_eightP
    (p : ℕ) [OddPrime p] (hGA : GriessAllModelsStatement) {Y : Type} [Group Y] [Finite Y]
    {L P : Subgroup Y} [L.Normal] (hCP : CompParab L P)
    (e8 : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8))
    (hrk : Open.pRank p (wPre P) ≤ 1) : LeviInnAtPW p P := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
      ((CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff _).2 ⟨e8⟩)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
  obtain ⟨ρ, hρs, -, hρ⟩ :=
    kFactCoverLinear_of_griess hGA Y L hCP.comp hCP.odd 4 K (by norm_num) e
  obtain ⟨σ, e', I, hσs, hσ, hI, hcomap, hIne, -⟩ :=
    CFSG.AGLEmbedding.exists_comap_eq_flagStabilizer hCP.odd (by norm_num) e hρs hρ hCP.parab
  have hIne' := hIne hCP.ne_top
  have hker : σ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 4) K) := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have h1 : LocalAnalysis.ComponentInitial.LinearFlag.proj 4 K g = 1 := by
      rw [← hσ g, hg, QuotientGroup.mk_one, map_one]
    exact LocalAnalysis.ComponentInitial.LinearFlag.scalars_le_center 4 K
      (LocalAnalysis.ComponentInitial.LinearFlag.proj_eq_one_iff.1 h1)
  exact leviInnAtW_of_levi_dataP (OddPrime.ne_two p) (K := SpecialLinearGroup (Fin 4) K)
    (G := fun a : Fin 4 => GL (Fin (linBlockLen 4 I a)) K) hCP.parab.1 hCP.odd σ hσs hker
    (odd_card_ker_of_le_center (by norm_num) σ hker) (flagStabilizer 4 K I) hcomap.symm
    (linBlockSL K 4 I) (fun _ => ⊤) (linLeviHom K 4 I) (isPGroup_ker_linLeviHom (by omega))
    pi_le_range_linLeviHom commutator_range_linLeviHom_le odd_relIndex_linLeviHom
    linBlockSL_bot_or_wBlock (fun _ _ => Subgroup.mem_top _)
    (fun a ha => blockOKP_linBlockSL a ha)
    (fun j E _ _ _ x hρx hβx => eq_one_of_mem_map_mulSingle hI hIne' x (hker hρx) hβx)
    (fun j _ x hρx hβx => by rw [eq_one_of_mem_map_mulSingle hI hIne' x (hker hρx) hβx, map_one])
    hrk

theorem fieldIndexOnPW_small (p : ℕ) [OddPrime p]
    (hGA : GriessAllModelsStatement) :
    FieldIndexOnPW p IsSmallTwoOrG2 := by
  intro Y _ _ L P hCP hS hLn hrank h3 hrk a ha3 haN hout
  haveI := hLn
  rcases (CFSG.HardMathSupport.Curtis.Proving.isSmallTwoOrG2_iff _).mp hS with h4 | hA8
  · exfalso
    obtain ⟨k, hk⟩ := ha3 ⟨a, Subgroup.mem_zpowers a⟩
    have hak : a ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact hout (exists_inner_wPre_of_oddInnW
      (oddInnW_of_overgroupOrder96 hCP
        (CFSG.HardMathSupport.Curtis.Proving.ordBound_isSmallFourTwo h4)) haN
      ((OddPrime.odd_pow p k).of_dvd_nat (orderOf_dvd_of_pow_eq_one hak)))
  · obtain ⟨eA⟩ := hA8
    exact fieldIndexW_of_outPNiceP hCP (outPNiceP_of_index_two p (index_inn_of_alt_eight eA))
      (leviInnAtW_alt_eightP p hGA hCP eA hrk) ha3 haN hout

end CFSG.LocalAnalysis.RankThreeTheoremC.FieldIndexW
