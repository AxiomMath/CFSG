module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDOrbit
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDReduce
import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG CFSG.Open Subgroup
open scoped commutatorElement
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (s622_sylow_isSylowOf_of_fusion s622_le_sup_normalizer)

theorem p622_abstract_reduction {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {zb : Y} (hzb : orderOf zb = p) {Xs Vb Mb : Subgroup Y}
    (hzX : zb ∈ Subgroup.normalizer (Xs : Set Y)) (hpX : ¬ p ∣ Nat.card Xs)
    (hV : CFSG.ABGLocalTools.IsSylowOf 2 Vb Xs) (hVz : zb ∈ Subgroup.normalizer (Vb : Set Y))
    (hVM : Vb ≤ Mb) (hKX : CFSG.Open.IsKGroup ↥Xs) (hodd : oddCore ↥Xs = ⊥)
    (hC : ∀ g ∈ Xs, zb * g = g * zb → g ∈ Mb)
    (hN : ∀ U : Subgroup Y, U ≤ Vb → U ≠ ⊥ → IsPGroup 2 U →
      zb ∈ Subgroup.normalizer (U : Set Y) → Subgroup.normalizer (U : Set Y) ⊓ Xs ≤ Mb)
    (hEven : KFactFieldAutEvenAt p) (hOdd : KFactFieldAutOddAt p) : Xs ≤ Mb := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp0 : 0 < p := hp.pos
  have hzp : zb ^ p = 1 := by rw [← hzb]; exact pow_orderOf_eq_one zb
  have hzN : ∀ i : ℕ, zb ^ i ∈ Subgroup.normalizer (Xs : Set Y) := fun i => pow_mem hzX i
  have hA : IsPGroup p (Subgroup.zpowers zb) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, hzb, pow_one]⟩
  have hbotp : IsPGroup 2 (⊥ : Subgroup Y) := IsPGroup.of_card (n := 0) (by simp)
  have hF2gen : ∀ U : Subgroup Y, U ≤ Xs → IsPGroup 2 U → U ≠ ⊥ →
      zb ∈ Subgroup.normalizer (U : Set Y) → Subgroup.normalizer (U : Set Y) ⊓ Xs ≤ Mb :=
    fun U hUX hU2 hU1 hzU =>
      normalizer_inf_le_of_invariant hp hzp hp0 hA hzX hpX hV hVz hC hN hUX hU2 hU1 hzU
  by_cases hQ : pCore 2 ↥Xs = ⊥
  swap
  · set Q : Subgroup Y := (pCore 2 ↥Xs).map Xs.subtype with hQdef
    have hQX : Q ≤ Xs := Subgroup.map_subtype_le _
    have hQ2 : IsPGroup 2 Q := (pCore_isPGroup (G := ↥Xs) (p := 2)).map Xs.subtype
    have hQne : Q ≠ ⊥ := by
      intro h
      apply hQ
      apply Subgroup.map_injective Xs.subtype_injective
      rw [Subgroup.map_bot]
      exact h
    have hchar : (pCore 2 ↥Xs).map (conjSubEquiv Xs hzX).toMonoidHom = pCore 2 ↥Xs :=
      Subgroup.characteristic_iff_map_eq.mp inferInstance (conjSubEquiv Xs hzX)
    have hQz : zb ∈ Subgroup.normalizer (Q : Set Y) := by
      apply mem_normalizer_of_forward hp0 hzp
      rintro _ ⟨w, hw, rfl⟩
      have hσ : conjSubEquiv Xs hzX w ∈ pCore 2 ↥Xs := by
        rw [← hchar]
        exact Subgroup.mem_map_of_mem _ hw
      exact Subgroup.mem_map.mpr ⟨conjSubEquiv Xs hzX w, hσ, rfl⟩
    have hQn : (Q.subgroupOf Xs).Normal := by
      have hsub : Q.subgroupOf Xs = pCore 2 ↥Xs :=
        Subgroup.comap_map_eq_self_of_injective Xs.subtype_injective _
      rw [hsub]
      infer_instance
    have hXQ : Xs ≤ Subgroup.normalizer (Q : Set Y) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQX).mp hQn
    intro x hx
    exact hF2gen Q hQX hQ2 hQne hQz ⟨hXQ hx, hx⟩
  by_cases hXbot : Xs = ⊥
  · rw [hXbot]
    exact bot_le
  haveI : Nontrivial ↥Xs := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXbot
    exact ⟨⟨a, 1, ha⟩⟩
  have hcomp : ∀ K : Subgroup ↥Xs, IsComponent K → K.map Xs.subtype ≤ Mb := by
    intro K hK
    have hKb : K.map Xs.subtype ≤ Xs := Subgroup.map_subtype_le K
    have hKnab : ¬ ∀ a b : ↥K, a * b = b * a := nonabelian_of_component hK
    haveI hKsimp : IsSimpleGroup ↥K := isSimpleGroup_of_component hQ hodd hK
    let e : ↥K ≃* ↥(K.map Xs.subtype) := K.equivMapOfInjective Xs.subtype Xs.subtype_injective
    have hsimpKb : IsSimpleGroup ↥(K.map Xs.subtype) :=
      (MulEquiv.isSimpleGroup_congr e).mp hKsimp
    have hnabKb : ¬ ∀ a b : ↥(K.map Xs.subtype), a * b = b * a := by
      intro h
      apply hKnab
      intro a b
      apply e.injective
      exact h (e a) (e b)
    have hKKb : CFSG.Open.IsKGroup ↥(K.map Xs.subtype) :=
      CFSG.Open.IsKGroup.of_surjective (hKX.subgroup K) e.toMonoidHom e.surjective
    have hpKb : ¬ p ∣ Nat.card ↥(K.map Xs.subtype) :=
      fun h => hpX (h.trans (Subgroup.card_dvd_of_le hKb))
    by_cases hnorm : zb ∈ Subgroup.normalizer ((K.map Xs.subtype : Subgroup Y) : Set Y)
    ·
      have hLz : ∀ g : Y, g ∈ K.map Xs.subtype ↔ zb * g * zb⁻¹ ∈ K.map Xs.subtype :=
        fun g => Subgroup.mem_normalizer_iff.mp hnorm g
      obtain ⟨S, hS, -, hzS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing hp
        Nat.prime_two hA hpKb (Subgroup.zpowers_le.mpr hnorm) bot_le hbotp
        (CFSG.Goldschmidt.G310.le_normalizer_of_normal (K := ⊥))
      have hTL : CFSG.ABGLocalTools.IsSylowOf 2 S (K.map Xs.subtype) :=
        s622_sylow_isSylowOf_of_fusion hS
      have hzS' : zb ∈ Subgroup.normalizer (S : Set Y) := hzS (Subgroup.mem_zpowers zb)
      have hTz : ∀ g ∈ S, zb * g * zb⁻¹ ∈ S :=
        fun g hg => (Subgroup.mem_normalizer_iff.mp hzS' g).mp hg
      have hC' : ∀ g ∈ K.map Xs.subtype, zb * g = g * zb → g ∈ Mb :=
        fun g hg hcg => hC g (hKb hg) hcg
      have hN1' : ∀ U : Subgroup Y, U ≤ S → U ≠ ⊥ → (∀ g ∈ U, zb * g * zb⁻¹ ∈ U) →
          Subgroup.normalizer (U : Set Y) ⊓ K.map Xs.subtype ≤ Mb := by
        intro U hUS hU1 hUz
        have hUX : U ≤ Xs := hUS.trans (hTL.le.trans hKb)
        have hU2 : IsPGroup 2 U := hTL.isPGroup.to_le hUS
        exact (inf_le_inf_left _ hKb).trans
          (hF2gen U hUX hU2 hU1 (mem_normalizer_of_forward hp0 hzp hUz))
      have hN3' : ∀ U : Subgroup Y, U ≤ K.map Xs.subtype → IsPGroup 2 U → U ≠ ⊥ →
          (∀ g ∈ U, zb * g = g * zb) →
          Subgroup.normalizer (U : Set Y) ⊓ K.map Xs.subtype ≤ Mb := by
        intro U hUK hU2 hU1 hUc
        have hzU : zb ∈ Subgroup.normalizer (U : Set Y) := by
          apply mem_normalizer_of_forward hp0 hzp
          intro g hg
          rw [hUc g hg, mul_assoc, mul_inv_cancel, mul_one]
          exact hg
        exact (inf_le_inf_left _ hKb).trans (hF2gen U (hUK.trans hKb) hU2 hU1 hzU)
      exact p622_le_of_orbit_length_one zb p hp hp2 hzp (K.map Xs.subtype) hLz hsimpKb hnabKb hKKb
        hpKb S hTL hTz Mb hC' hN1' hN3' hEven hOdd
    ·
      set J₀ : Subgroup Y := ⨆ (i : ℕ) (_ : i < p), conjPow zb i (K.map Xs.subtype) with hJ₀
      have hconjX : ∀ i : ℕ, conjPow zb i (K.map Xs.subtype) ≤ Xs := by
        intro i x hx
        obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
        exact (Subgroup.mem_normalizer_iff.mp (hzN i) k).mp (hKb hk)
      have hJ0 : ∀ i : ℕ, i < p → conjPow zb i (K.map Xs.subtype) ≤ J₀ := fun i hi =>
        le_iSup₂ (f := fun (i : ℕ) (_ : i < p) => conjPow zb i (K.map Xs.subtype)) i hi
      have hJX : J₀ ≤ Xs := iSup₂_le fun i _ => hconjX i
      have hC' : ∀ g ∈ J₀, zb * g = g * zb → g ∈ Mb := fun g hg hcg => hC g (hJX hg) hcg
      have hcomm : ∀ i : ℕ, 0 < i → i < p → ∀ x ∈ K.map Xs.subtype,
          ∀ y ∈ conjPow zb i (K.map Xs.subtype), x * y = y * x := by
        intro i hi0 hip x hx y hy
        have hK' : IsComponent (K.map (conjSubEquiv Xs (hzN i)).toMonoidHom) :=
          LocalCores.isComponent_map_mulEquiv _ hK
        have himg : ((K.map (conjSubEquiv Xs (hzN i)).toMonoidHom).map Xs.subtype) =
            conjPow zb i (K.map Xs.subtype) := map_map_conjSubEquiv (hzN i) K
        have hKK' : K ≠ K.map (conjSubEquiv Xs (hzN i)).toMonoidHom := by
          intro hEq
          apply hnorm
          apply mem_normalizer_of_pow_eq hp hzp hi0 hip
          rw [← himg, ← hEq]
        rcases LocalCores.distinct_components_commute hK hK' with h | h
        · exact absurd h hKK'
        · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
          have hy' : y ∈ (K.map (conjSubEquiv Xs (hzN i)).toMonoidHom).map Xs.subtype := by
            rw [himg]
            exact hy
          obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy'
          have hab : ⁅a, b⁆ = 1 := by
            have hmem := Subgroup.commutator_mem_commutator ha hb
            rw [h, Subgroup.mem_bot] at hmem
            exact hmem
          exact congrArg Subtype.val (commutatorElement_eq_one_iff_mul_comm.mp hab)
      have hTL : Vb ⊓ K.map Xs.subtype ≠ ⊥ := by
        obtain ⟨x, hx1, hxV, hxK⟩ := exists_mem_sylow_component hV hQ hodd hK
        refine Subgroup.ne_bot_iff_exists_ne_one.mpr
          ⟨⟨(x : Y), ⟨hxV, Subgroup.mem_map.mpr ⟨x, hxK, rfl⟩⟩⟩, fun h => hx1 ?_⟩
        apply Subtype.ext
        simpa using congrArg Subtype.val h
      exact le_of_orbit_length_p zb p hp0 hzp (K.map Xs.subtype) hsimpKb Mb Vb J₀ hJ0 hcomm
        hC' hVM hTL
  have hEMb : (layer ↥Xs).map Xs.subtype ≤ Mb := by
    rw [Subgroup.map_le_iff_le_comap, layer.eq_sSup]
    apply sSup_le
    intro K hK
    exact Subgroup.map_le_iff_le_comap.mp (hcomp K hK)
  obtain ⟨K₀, hK₀⟩ := exists_component_of_cores hQ hodd
  have hEnorm : (layer ↥Xs).Normal := layer_normal_of_group ↥Xs
  have hEtop : (⊤ : Subgroup ↥Xs) ≤ normalizer ((layer ↥Xs : Subgroup ↥Xs) : Set ↥Xs) :=
    le_of_eq (Subgroup.normalizer_eq_top_iff.mpr hEnorm).symm
  have hVs := isSylowOf_subgroupOf_top hV
  have hWs : CFSG.ABGLocalTools.IsSylowOf 2 (Vb.subgroupOf Xs ⊓ layer ↥Xs) (layer ↥Xs) :=
    hVs.inf_of_le_normalizer le_top hEtop
  have hKE : K₀ ≤ layer ↥Xs := by
    rw [layer.eq_sSup]
    exact le_sSup hK₀
  have hWne : Vb.subgroupOf Xs ⊓ layer ↥Xs ≠ ⊥ := by
    obtain ⟨x, hx1, hxV, hxK⟩ := exists_mem_sylow_component hV hQ hodd hK₀
    intro h
    have hxW : x ∈ Vb.subgroupOf Xs ⊓ layer ↥Xs :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hxV, hKE hxK⟩
    rw [h, Subgroup.mem_bot] at hxW
    exact hx1 hxW
  have hNE : ((layer ↥Xs).subgroupOf (⊤ : Subgroup ↥Xs)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mpr hEtop
  have hfr := s622_le_sup_normalizer Nat.prime_two (le_top : layer ↥Xs ≤ ⊤) hNE hWs
  have hσ : ∀ w ∈ Vb.subgroupOf Xs ⊓ layer ↥Xs,
      conjSubEquiv Xs hzX w ∈ Vb.subgroupOf Xs ⊓ layer ↥Xs := by
    intro w hw
    obtain ⟨hwV, hwE⟩ := Subgroup.mem_inf.mp hw
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hVz (w : Y)).mp (Subgroup.mem_subgroupOf.mp hwV)
    · have hchar : (layer ↥Xs).map (conjSubEquiv Xs hzX).toMonoidHom = layer ↥Xs :=
        Subgroup.characteristic_iff_map_eq.mp LocalCores.layer_characteristic
          (conjSubEquiv Xs hzX)
      rw [← hchar]
      exact Subgroup.mem_map_of_mem _ hwE
  have hNW : normalizer ((Vb.subgroupOf Xs ⊓ layer ↥Xs : Subgroup ↥Xs) : Set ↥Xs) ⊓ ⊤ ≤
      Mb.comap Xs.subtype := by
    rintro x ⟨hxN, -⟩
    have hWbX : (Vb.subgroupOf Xs ⊓ layer ↥Xs).map Xs.subtype ≤ Xs := Subgroup.map_subtype_le _
    have hW' : ((Vb.subgroupOf Xs ⊓ layer ↥Xs).map Xs.subtype).subgroupOf Xs =
        Vb.subgroupOf Xs ⊓ layer ↥Xs :=
      Subgroup.comap_map_eq_self_of_injective Xs.subtype_injective _
    have hxWb : (x : Y) ∈ Subgroup.normalizer
        (((Vb.subgroupOf Xs ⊓ layer ↥Xs).map Xs.subtype : Subgroup Y) : Set Y) := by
      have h1 := Subgroup.subgroupOf_normalizer_eq hWbX
      rw [hW'] at h1
      have h2 : x ∈ (Subgroup.normalizer
          (((Vb.subgroupOf Xs ⊓ layer ↥Xs).map Xs.subtype : Subgroup Y) : Set Y)).subgroupOf
            Xs := by
        rw [h1]
        exact hxN
      exact Subgroup.mem_subgroupOf.mp h2
    have hWbV : (Vb.subgroupOf Xs ⊓ layer ↥Xs).map Xs.subtype ≤ Vb := by
      intro y hy
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hw).1
    have hWbne : (Vb.subgroupOf Xs ⊓ layer ↥Xs).map Xs.subtype ≠ ⊥ := by
      intro h
      apply hWne
      apply Subgroup.map_injective Xs.subtype_injective
      rw [h, Subgroup.map_bot]
    have hWb2 : IsPGroup 2 ((Vb.subgroupOf Xs ⊓ layer ↥Xs).map Xs.subtype) :=
      hWs.isPGroup.map Xs.subtype
    have hzWb : zb ∈ Subgroup.normalizer
        (((Vb.subgroupOf Xs ⊓ layer ↥Xs).map Xs.subtype : Subgroup Y) : Set Y) := by
      apply mem_normalizer_of_forward hp0 hzp
      rintro _ ⟨w, hw, rfl⟩
      exact Subgroup.mem_map.mpr ⟨conjSubEquiv Xs hzX w, hσ w hw, rfl⟩
    exact Subgroup.mem_comap.mpr (hN _ hWbV hWbne hWb2 hzWb ⟨hxWb, x.2⟩)
  intro y hy
  exact (sup_le (Subgroup.map_le_iff_le_comap.mp hEMb) hNW) (hfr (Subgroup.mem_top ⟨y, hy⟩))

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
