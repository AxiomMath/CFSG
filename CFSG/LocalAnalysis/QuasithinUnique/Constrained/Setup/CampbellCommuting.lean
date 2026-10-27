module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellAdapter
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.BlueprintB2
open scoped commutatorElement

section Tools

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conj_mem {K : Subgroup G} {g : G}
    (h : ∀ x ∈ K, g * x * g⁻¹ ∈ K) (h' : ∀ x ∈ K, g⁻¹ * x * g ∈ K) :
    g ∈ normalizer (K : Set G) :=
  Subgroup.mem_normalizer_iff.mpr fun x =>
    ⟨fun hx => h x hx, fun hx => by simpa [mul_assoc] using h' _ hx⟩

theorem signalizer_action_ambient [Finite G] {H K R : Subgroup G} (hKH : K ≤ H)
    (hsub : (K.subgroupOf H).IsSubnormal) (hno : NoPQuotient 2 K) (hR : IsPGroup 2 R)
    (hRH : R ≤ H) (hKR : K ≤ normalizer (R : Set G)) :
    R ≤ normalizer (K : Set G) ∧ ⁅K, R⁆ ≤ pCoreOf 2 K := by
  classical
  have hno' : NoPQuotient 2 (K.subgroupOf H) :=
    NoPQuotient.of_surjective (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective hno
  have hR' : IsPGroup 2 (R.subgroupOf H) :=
    hR.of_surjective (Subgroup.subgroupOfEquivOfLe hRH).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hRH).symm.surjective
  have hKR' : K.subgroupOf H ≤ normalizer ((R.subgroupOf H : Subgroup H) : Set H) := by
    intro x hx
    refine mem_normalizer_of_conj_mem (fun y hy => ?_) (fun y hy => ?_)
    · have hxK : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx
      have hyR : (y : G) ∈ R := Subgroup.mem_subgroupOf.mp hy
      exact Subgroup.mem_subgroupOf.mpr
        ((Subgroup.mem_normalizer_iff.mp (hKR hxK) (y : G)).mp hyR)
    · have hxK : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx
      have hyR : (y : G) ∈ R := Subgroup.mem_subgroupOf.mp hy
      have := (Subgroup.mem_normalizer_iff.mp (hKR (K.inv_mem hxK)) (y : G)).mp hyR
      exact Subgroup.mem_subgroupOf.mpr (by simpa using this)
  obtain ⟨h1, h2⟩ := prime_residual_subnormal_p_signalizer_action hsub hno' hR' hKR'
  refine ⟨?_, ?_⟩
  · intro r hr
    have hr' : (⟨r, hRH hr⟩ : H) ∈ normalizer ((K.subgroupOf H : Subgroup H) : Set H) :=
      h1 (Subgroup.mem_subgroupOf.mpr hr)
    refine mem_normalizer_of_conj_mem (fun x hx => ?_) (fun x hx => ?_)
    · have := (Subgroup.mem_normalizer_iff.mp hr' ⟨x, hKH hx⟩).mp (Subgroup.mem_subgroupOf.mpr hx)
      exact Subgroup.mem_subgroupOf.mp this
    · have hr'' : (⟨r, hRH hr⟩ : H)⁻¹ ∈ normalizer ((K.subgroupOf H : Subgroup H) : Set H) :=
        inv_mem hr'
      have := (Subgroup.mem_normalizer_iff.mp hr'' ⟨x, hKH hx⟩).mp (Subgroup.mem_subgroupOf.mpr hx)
      have h4 := Subgroup.mem_subgroupOf.mp this
      simpa using h4
  · have h3 := Subgroup.map_mono (f := H.subtype) h2
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKH,
      Subgroup.map_subgroupOf_eq_of_le hRH,
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_map_subtype 2 H (K.subgroupOf H),
      Subgroup.map_subgroupOf_eq_of_le hKH] at h3
    exact h3

theorem conjSubgroup_iSup {ι : Sort*} (A : ι → Subgroup G) (g : G) :
    conjSubgroup (⨆ i, A i) g = ⨆ i, conjSubgroup (A i) g := by
  simp only [C5.conjSubgroup_def]
  exact Subgroup.map_iSup _ _

theorem mem_normalizer_iSup {ι : Sort*} (A : ι → Subgroup G) {g : G}
    (h : ∀ i, g ∈ normalizer (A i : Set G)) :
    g ∈ normalizer ((⨆ i, A i : Subgroup G) : Set G) := by
  rw [← conjSubgroup_eq_iff_mem_normalizer, conjSubgroup_iSup]
  exact iSup_congr fun i => C5.conjSubgroup_eq_self (h i)

theorem mem_normalizer_iSup_of_perm {ι : Sort*} (A : ι → Subgroup G) {g : G}
    (h1 : ∀ i, ∃ j, conjSubgroup (A i) g = A j) (h2 : ∀ i, ∃ j, conjSubgroup (A i) g⁻¹ = A j) :
    g ∈ normalizer ((⨆ i, A i : Subgroup G) : Set G) := by
  have hle : ∀ g' : G, (∀ i, ∃ j, conjSubgroup (A i) g' = A j) →
      conjSubgroup (⨆ i, A i) g' ≤ ⨆ i, A i := by
    intro g' hg'
    rw [conjSubgroup_iSup]
    refine iSup_le fun i => ?_
    obtain ⟨j, hj⟩ := hg' i
    rw [hj]
    exact le_iSup A j
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  refine le_antisymm (hle g h1) ?_
  have := C5.conjSubgroup_mono (hle g⁻¹ h2) g
  rwa [C5.conjSubgroup_inv_conjSubgroup] at this

theorem conjSubgroup_blockQ (L : Subgroup G) (g : G) :
    conjSubgroup (blockQ L) g = blockQ (conjSubgroup L g) :=
  C5.conjSubgroup_pCoreOf 2 L g

theorem conjSubgroup_blockU (L : Subgroup G) (g : G) :
    conjSubgroup (blockU L) g = blockU (conjSubgroup L g) := by
  unfold blockU
  rw [C5.conjSubgroup_commutator, conjSubgroup_blockQ]

theorem blockU_ne_bot_of_isShort2 {L : Subgroup G} (hL : IsShort2 L) : blockU L ≠ ⊥ := by
  intro h
  have h5 := hL.2.2.2.2.1
  rw [h] at h5
  exact not_lt_bot h5

theorem blockU_le_self_of_isShort2 {L : Subgroup G} (hL : IsShort2 L) : blockU L ≤ L :=
  (C1.blockU_le_blockQ hL).trans (C1.blockQ_le L)

theorem le_normalizer_of_commute {A B C : Subgroup G} (hAB : A ≤ B)
    (h : ∀ x ∈ B, ∀ y ∈ C, Commute x y) : C ≤ normalizer (A : Set G) := by
  intro y hy
  refine mem_normalizer_of_conj_mem (fun a ha => ?_) (fun a ha => ?_)
  · have e : y * a * y⁻¹ = a := (h a (hAB ha) y hy).symm.mul_inv_cancel
    rw [e]
    exact ha
  · have e : y⁻¹ * a * y = a := by
      have hc : Commute y⁻¹ a := (h a (hAB ha) y hy).symm.inv_left
      simpa using hc.mul_inv_cancel
    rw [e]
    exact ha

theorem conj_mem_centerTorsion {p : ℕ} {Q : Subgroup G} {g : G} (hg : g ∈ normalizer (Q : Set G))
    {z : G} (hz : z ∈ centerTorsion p Q) : g * z * g⁻¹ ∈ centerTorsion p Q := by
  obtain ⟨hzQ, hzc, hzp⟩ := mem_centerTorsion_iff.mp hz
  refine mem_centerTorsion_iff.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hzQ,
    fun k hk => ?_, ?_⟩
  · have hk' : g⁻¹ * k * g ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) k).mp hk
      simpa using this
    have h1 := hzc _ hk'
    calc k * (g * z * g⁻¹) = g * ((g⁻¹ * k * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
      _ = g * z * g⁻¹ * k := by group
  · rw [conj_pow, hzp]
    simp

theorem mem_normalizer_centerTorsion {p : ℕ} {Q : Subgroup G} {g : G}
    (hg : g ∈ normalizer (Q : Set G)) :
    g ∈ normalizer ((centerTorsion p Q : Subgroup G) : Set G) :=
  mem_normalizer_of_conj_mem (fun _ hz => conj_mem_centerTorsion hg hz)
    (fun _ hz => by simpa using conj_mem_centerTorsion (inv_mem hg) hz)

end Tools

section Join

variable {G : Type*} [Group G]

theorem exists_noncommProd_of_mem_iSup {ι : Type*} [Fintype ι] (L : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, Commute x y) {x : G} (hx : x ∈ ⨆ i, L i) :
    ∃ g : ι → G, (∀ i, g i ∈ L i) ∧
      ∃ hg : (↑(Finset.univ : Finset ι) : Set ι).Pairwise (Function.onFun Commute g),
        x = Finset.univ.noncommProd g hg := by
  classical
  have hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ L i → y ∈ L j → Commute x y :=
    fun i j hij x y hx hy => hc i j hij x hx y hy
  have hmem : x ∈ (Subgroup.noncommPiCoprod hcomm).range := by
    rw [Subgroup.noncommPiCoprod_range]
    exact hx
  obtain ⟨F, hF⟩ := hmem
  refine ⟨fun i => (F i : G), fun i => (F i).2,
    fun i _ j _ hij => hc i j hij _ (F i).2 _ (F j).2, ?_⟩
  rw [← hF]
  rfl

end Join

section Main

variable {G : Type*} [Group G] [Finite G]

theorem inf_centralizer_blockU_eq_blockQ {L : Subgroup G} (hL : IsShort2 L) :
    L ⊓ centralizer (blockU L : Set G) = blockQ L := by
  refine le_antisymm (C1.inf_centralizer_blockU_le hL) (le_inf (C1.blockQ_le L) ?_)
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact C1.blockU_comm hL u hu q hq

theorem commuting_short_product_core_centralizer {H T : Subgroup G} (hT : IsSylowTwoOf T H)
    {s : ℕ} (hs : 1 ≤ s) (L : Fin s → Subgroup G) (hL : ∀ i, IsBlock2 H (L i))
    (hcomm : ∀ i j, i ≠ j → ⁅L i, L j⁆ = ⊥)
    (hperm : ∀ t ∈ T, ∀ i, ∃ j, conjSubgroup (L i) t = L j)
    (hKT : (⨆ i, L i) ⊔ T = H) :
    (⨆ i, blockU (L i)) ≠ ⊥ ∧ IsElemAbelian 2 (⨆ i, blockU (L i) : Subgroup G) ∧
      H ≤ normalizer ((⨆ i, blockU (L i) : Subgroup G) : Set G) ∧
      H ⊓ centralizer ((⨆ i, blockU (L i) : Subgroup G) : Set G) = blockQ H ∧
      (⨆ i, blockU (L i) : Subgroup G) ≤ centerTorsion 2 (blockQ H) ∧
      T ⊓ centralizer ((⨆ i, blockU (L i) : Subgroup G) : Set G) = blockQ H ∧
      ∀ i, L i ⊓ centralizer (blockU (L i) : Set G) = blockQ (L i) := by
  classical
  set K : Subgroup G := ⨆ i, L i with hK
  set U : Subgroup G := ⨆ i, blockU (L i) with hU
  set P : Subgroup G := blockQ H with hP
  have hLH : ∀ i, L i ≤ H := fun i => (hL i).2.1
  have hsubn : ∀ i, ((L i).subgroupOf H).IsSubnormal := fun i => (hL i).2.2
  have hshort : ∀ i, IsShort2 (L i) := fun i => (hL i).1
  have hTH : T ≤ H := hT.1
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hcomm' : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, Commute x y := by
    intro i j hij x hx y hy
    have hx' : x ∈ centralizer (L j : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm i j hij) hx
    exact (Subgroup.mem_centralizer_iff.mp hx' y hy).symm
  have hTK : T ≤ normalizer (K : Set G) := fun t ht =>
    mem_normalizer_iSup_of_perm L (hperm t ht) (hperm t⁻¹ (T.inv_mem ht))
  have hperm' : ∀ t ∈ T, ∀ i, ∃ j, conjSubgroup (blockU (L i)) t = blockU (L j) := by
    intro t ht i
    obtain ⟨j, hj⟩ := hperm t ht i
    exact ⟨j, by rw [conjSubgroup_blockU, hj]⟩
  have hTU : T ≤ normalizer (U : Set G) := fun t ht =>
    mem_normalizer_iSup_of_perm (fun i => blockU (L i)) (hperm' t ht)
      (hperm' t⁻¹ (T.inv_mem ht))
  have hLnorm : ∀ i j, i ≠ j → ∀ A : Subgroup G, A ≤ L i → L j ≤ normalizer (A : Set G) :=
    fun i j hij A hA => le_normalizer_of_commute hA (fun x hx y hy => hcomm' i j hij x hx y hy)
  have hKU : K ≤ normalizer (U : Set G) := by
    refine iSup_le fun j x hx => ?_
    refine mem_normalizer_iSup (fun i => blockU (L i)) (fun i => ?_)
    by_cases hij : i = j
    · subst hij
      exact C1.le_normalizer_blockU (L i) hx
    · exact hLnorm i j hij _ (blockU_le_self_of_isShort2 (hshort i)) hx
  have hHU : H ≤ normalizer (U : Set G) := by
    have : K ⊔ T ≤ normalizer (U : Set G) := sup_le hKU hTU
    rwa [hKT] at this
  have hP2 : IsPGroup 2 P := C1.blockQ_isPGroup H
  have hPH : P ≤ H := C1.blockQ_le H
  have hPn : H ≤ normalizer (P : Set G) := C1.le_normalizer_blockQ H
  have hUiP : ∀ i, blockU (L i) ≤ P := fun i =>
    (C1.blockU_le_blockQ (hshort i)).trans (pCoreOf_le_of_isSubnormal 2 (hLH i) (hsubn i))
  have hsig : ∀ i, P ≤ normalizer (L i : Set G) ∧ ⁅L i, P⁆ ≤ blockQ (L i) := fun i =>
    signalizer_action_ambient (hLH i) (hsubn i) (hshort i).1 hP2 hPH ((hLH i).trans hPn)
  have hPcU : ∀ i, ∀ y ∈ P, ∀ u ∈ blockU (L i), u * y = y * u := by
    intro i y hy
    refine C1.commute_blockU_of_mem (hshort i) ((hsig i).1 hy)
      (C1.exists_pow_eq_one_of_isPGroup hP2 hy) ?_
    intro l hl
    have hmem : ⁅y, l⁆ ∈ ⁅P, L i⁆ := Subgroup.commutator_mem_commutator hy hl
    rw [Subgroup.commutator_comm] at hmem
    exact (hsig i).2 hmem
  have hPU : P ≤ centralizer (U : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    refine Subgroup.iSup_induction (fun i => blockU (L i)) (C := fun u => u * y = y * u) hu
      ?_ ?_ ?_
    · intro i u hu
      exact hPcU i y hy u hu
    · simp
    · intro a b ha hb
      calc a * b * y = a * (b * y) := mul_assoc _ _ _
        _ = a * (y * b) := by rw [hb]
        _ = (a * y) * b := (mul_assoc _ _ _).symm
        _ = (y * a) * b := by rw [ha]
        _ = y * (a * b) := mul_assoc _ _ _
  have hUP : U ≤ P := iSup_le hUiP
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    intro a ha b hb
    exact ((Subgroup.mem_centralizer_iff.mp (hPU (hUP ha))) b hb).symm
  have hU2 : ∀ x ∈ U, x ^ 2 = 1 := by
    intro x hx
    have key : x ∈ U ∧ x ^ 2 = 1 := by
      refine Subgroup.iSup_induction (fun i => blockU (L i))
        (C := fun x => x ∈ U ∧ x ^ 2 = 1) hx ?_ ?_ ?_
      · intro i x hx
        exact ⟨Subgroup.mem_iSup_of_mem i hx, C1.blockU_sq (hshort i) x hx⟩
      · exact ⟨one_mem _, one_pow 2⟩
      · rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have hc : Commute a b := hUab a ha b hb
        rw [hc.mul_pow, ha2, hb2, one_mul]
    exact key.2
  have hUne : U ≠ ⊥ := by
    intro h
    have h0 : blockU (L ⟨0, hs⟩) ≤ U := le_iSup (fun i => blockU (L i)) ⟨0, hs⟩
    rw [h, le_bot_iff] at h0
    exact blockU_ne_bot_of_isShort2 (hshort ⟨0, hs⟩) h0
  have hKnorm : ∀ i, K ≤ normalizer (blockQ (L i) : Set G) := by
    intro i
    refine iSup_le fun j x hx => ?_
    by_cases hij : i = j
    · subst hij
      exact C1.le_normalizer_blockQ (L i) hx
    · exact hLnorm i j hij _ (C1.blockQ_le (L i)) hx
  have hQK : ∀ i, blockQ (L i) ≤ pCoreOf 2 K := fun i =>
    C1.le_pCoreOf_of_normalized ((C1.blockQ_le (L i)).trans (le_iSup L i)) (hKnorm i)
      (C1.blockQ_isPGroup (L i))
  have hCP : H ⊓ centralizer (U : Set G) ≤ P := by
    set C : Subgroup G := H ⊓ centralizer (U : Set G) with hC
    have hCH : C ≤ H := inf_le_left
    have hCn : (C.subgroupOf H).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCH]
      intro x hx
      exact C5.mem_normalizer_inf (Subgroup.le_normalizer hx)
        (C5.mem_normalizer_centralizer (hHU hx))
    have hodd : ∀ c ∈ C, Odd (orderOf c) → c = 1 := by
      intro c hc hco
      have hcH : c ∈ H := hCH hc
      have hcK : c ∈ K := by
        have hcKT : c ∈ K ⊔ T := by
          rw [hKT]
          exact hcH
        obtain ⟨m, hm⟩ := C1.exists_pow_mem_of_mem_sup hT2 hTK hcKT
        exact mem_of_odd_orderOf_of_pow_mem hco hm
      obtain ⟨g, hg, hgc, hcg⟩ := exists_noncommProd_of_mem_iSup L hcomm' hcK
      have hgQ : ∀ i, g i ∈ blockQ (L i) := by
        intro i
        have hgi : g i ∈ L i ⊓ centralizer (blockU (L i) : Set G) := by
          refine Subgroup.mem_inf.mpr ⟨hg i, ?_⟩
          rw [Subgroup.mem_centralizer_iff]
          intro u hu
          have hcu : u * c = c * u :=
            Subgroup.mem_centralizer_iff.mp hc.2 u (le_iSup (fun i => blockU (L i)) i hu)
          have hsplit : g i * (Finset.univ.erase i).noncommProd g (hgc.mono (by simp)) = c := by
            rw [hcg]
            exact Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ i) g hgc
          have hc'u : Commute u ((Finset.univ.erase i).noncommProd g (hgc.mono (by simp))) := by
            refine Finset.noncommProd_commute _ _ _ _ (fun j hj => ?_)
            have hji : i ≠ j := fun h => (Finset.mem_erase.mp hj).1 h.symm
            exact hcomm' i j hji u (blockU_le_self_of_isShort2 (hshort i) hu) (g j) (hg j)
          set c' := (Finset.univ.erase i).noncommProd g (hgc.mono (by simp)) with hc'
          have h1 : (g i * u) * c' = (u * g i) * c' := by
            calc (g i * u) * c' = g i * (u * c') := mul_assoc _ _ _
              _ = g i * (c' * u) := by rw [hc'u.eq]
              _ = (g i * c') * u := (mul_assoc _ _ _).symm
              _ = c * u := by rw [hsplit]
              _ = u * c := hcu.symm
              _ = u * (g i * c') := by rw [hsplit]
              _ = (u * g i) * c' := (mul_assoc _ _ _).symm
          exact (mul_right_cancel h1).symm
        rw [inf_centralizer_blockU_eq_blockQ (hshort i)] at hgi
        exact hgi
      have hcO : c ∈ blockQ K := by
        rw [hcg]
        exact Subgroup.noncommProd_mem _ hgc (fun i _ => hQK i (hgQ i))
      exact eq_one_of_isPGroup_of_odd (C1.blockQ_isPGroup K) hcO hco
    have hC2 : IsPGroup 2 C := isPGroup_two_of_forall_odd hodd
    exact le_pCoreOf_of_normal_subgroupOf 2 hCH hCn hC2
  have hCeq : H ⊓ centralizer (U : Set G) = P := le_antisymm hCP (le_inf hPH hPU)
  have hPT : P ≤ T := hT.pCoreOf_le
  have hUW : U ≤ centerTorsion 2 P := fun u hu =>
    mem_centerTorsion_iff.mpr ⟨hUP hu,
      fun k hk => (Subgroup.mem_centralizer_iff.mp (hPU hk) u hu).symm, hU2 u hu⟩
  refine ⟨hUne, C5.isElemAbelian_two_iff.mpr ⟨hUab, hU2⟩, hHU, hCeq, hUW, ?_, ?_⟩
  · refine le_antisymm (fun x hx => hCP ⟨hTH hx.1, hx.2⟩) (le_inf hPT hPU)
  · intro i
    exact inf_centralizer_blockU_eq_blockQ (hshort i)

end Main

end CFSG.QuasithinUnique.Setup.Campbell
