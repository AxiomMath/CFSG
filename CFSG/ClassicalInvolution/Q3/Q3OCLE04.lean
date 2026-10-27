module

public import CFSG.ClassicalInvolution.Q3.Q3OCLY01
public import CFSG.ClassicalInvolution.Q3.Q3OCLE03
public import CFSG.ClassicalInvolution.Q3.Q3OCLExact
public import CFSG.ClassicalInvolution.Q3.Q3T7S23Chain
public import CFSG.ClassicalInvolution.Q3.Q3T7LayerOdd

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OCL

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3T7.OddC

section Algebra

variable {G : Type} [Group G]

theorem le_normalizer_of_conj_mem {C N : Subgroup G} (h : ∀ c ∈ C, ∀ m ∈ N, c * m * c⁻¹ ∈ N) :
    C ≤ Subgroup.normalizer (N : Set G) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro m
  refine ⟨fun hm => h c hc m hm, fun hm => ?_⟩
  have := h c⁻¹ (C.inv_mem hc) _ hm
  simpa [mul_assoc] using this

end Algebra


section Frame

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}

theorem alphaOf_e_pair_eq_bot (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z)
    (hd : Q3T8.Asc77.Hyp23bData Ω K K' W z u e g)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) {y : G} (hy : y = z ∨ y = u) :
    alphaOf (Subgroup.closure ({e, y} : Set G)) = ⊥ := by
  obtain ⟨hzB, huB, heB⟩ := CFSG.ClassicalInvolution.Asc77.T7K.generators_mem_B z u e
  have hy2 : y * y = 1 := by
    rcases hy with rfl | rfl
    · exact hs.hz.sq
    · exact hd.hu2
  have hy1 : y ≠ 1 := by
    rcases hy with rfl | rfl
    · exact hs.hz.ne_one
    · exact hd.hu1
  have hyW : y ∈ W := by
    rcases hy with rfl | rfl
    · exact hd.hzW
    · exact hd.huW
  have hyK : y ∈ K ⊔ K' := by
    rcases hy with rfl | rfl
    · exact Subgroup.mem_sup_left hs.hz.mem
    · exact hd.hu
  have hye : y ≠ e := fun h => Q3T8.Asc77.T7K.e_not_mem_sup hs hd (h ▸ hyK)
  have hcomm : y * e = e * y := CFSG.ClassicalInvolution.Asc77.T7K.comm_e_of_mem_W hd hyW
  have hA : IsElemAbelian2 (Subgroup.closure ({y, e} : Set G)) 2 :=
    CFSG.ClassicalInvolution.Asc77.T7A.isElemAbelian2_closure_pair hy2 hd.he2 hy1 hd.he1 hye
      hcomm
  have hyB : y ∈ Subgroup.closure ({u * e, u, z} : Set G) := by
    rcases hy with rfl | rfl
    · exact hzB
    · exact huB
  have hAB : Subgroup.closure ({y, e} : Set G) ≤ Subgroup.closure ({u * e, u, z} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hyB
    · exact heB
  obtain ⟨-, halpha⟩ := Q3T8.Asc77.T7K.c23_5X_one_proved hs hd
  have hαA := (halpha _ hAB hA).trans hα
  rwa [Set.pair_comm] at hαA

theorem conjSub_le_centralizer_e3 (hd : Q3T8.Asc77.Hyp23bData Ω K K' W z u e g) {L : Subgroup G}
    (hL : L ≤ Subgroup.centralizer ({e} : Set G)) :
    conjSub g L ≤ Subgroup.centralizer ({e} : Set G) := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : (g⁻¹ * x * g) * e = e * (g⁻¹ * x * g) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hL hx)
  have h2 : g * e = e * g := CFSG.ClassicalInvolution.Asc77.T7K.comm_e hd
    (CFSG.ClassicalInvolution.Asc77.T7K.g_mem_normalizer hd)
  calc x * e = g * ((g⁻¹ * x * g) * e) * g⁻¹ := by
        have : g * ((g⁻¹ * x * g) * e) * g⁻¹ = x * (g * e * g⁻¹) := by group
        rw [this, h2]
        group
    _ = g * (e * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
    _ = e * x := by
        have : g * (e * (g⁻¹ * x * g)) * g⁻¹ = (g * e * g⁻¹) * x := by group
        rw [this, h2]
        group

theorem oddCore_e_centralizes (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z)
    (hd : Q3T8.Asc77.Hyp23bData Ω K K' W z u e g)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) (hex : ExactMembers Ω) {x : G}
    (hx : x ∈ oddCoreOf (Subgroup.centralizer ({e} : Set G))) :
    x * u = u * x ∧ (∀ m ∈ conjSub g K, x * m = m * x) ∧ (∀ m ∈ conjSub g K', x * m = m * x) := by
  classical
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hodd := odd_orderOf_of_mem_oddCoreOf hx
  have hcA : e ∈ Subgroup.closure ({e, u} : Set G) := Subgroup.subset_closure (by simp)
  have huA : u ∈ Subgroup.closure ({e, u} : Set G) := Subgroup.subset_closure (by simp)
  have hxu : x * u = u * x :=
    T7Y.commute_of_alphaOf_eq_bot hcA hd.he1 (alphaOf_e_pair_eq_bot hs hd hα (Or.inr rfl)) hx huA
  have hxe : x * e = e * x :=
    Subgroup.mem_centralizer_singleton_iff.mp (oddCoreOf_le_self _ hx)
  have ht : x * (u * e) * x⁻¹ = u * e := by
    calc x * (u * e) * x⁻¹ = (x * u) * e * x⁻¹ := by group
      _ = (u * x) * e * x⁻¹ := by rw [hxu]
      _ = u * (x * e) * x⁻¹ := by group
      _ = u * (e * x) * x⁻¹ := by rw [hxe]
      _ = u * e := by group
  have hV : ∀ M ∈ Ω, IsUniqueInvolution M z → M = K ∨ M = K' := by
    intro M hM hMz
    have hmem : M ∈ twinSet Ω K := ⟨hM, z, hs.hz, hMz⟩
    rw [hs.twinSet_eq] at hmem
    exact hmem
  have hVt : ∀ M ∈ Ω, IsUniqueInvolution M (u * e) → M = conjSub g K ∨ M = conjSub g K' := by
    intro M hM hMt
    have hM' : conjSub g⁻¹ M ∈ Ω := hΩ.conjInvariant g⁻¹ M hM
    have hMz : IsUniqueInvolution (conjSub g⁻¹ M) z := by
      have h1 := hMt.conj g⁻¹
      rwa [show g⁻¹ * (u * e) * (g⁻¹)⁻¹ = z by rw [← hd.hgt]; group] at h1
    have hMg : conjSub g (conjSub g⁻¹ M) = M := by simpa using conjSub_inv_conjSub g⁻¹ M
    rcases hV _ hM' hMz with h | h
    · left
      rw [← hMg, h]
    · right
      rw [← hMg, h]
  have hJΩ : conjSub g K ∈ Ω := hΩ.conjInvariant g K hKΩ
  have hJ'Ω : conjSub g K' ∈ Ω := hΩ.conjInvariant g K' hK'Ω
  have hJt : IsUniqueInvolution (conjSub g K) (u * e) := hd.hgt ▸ hs.hz.conj g
  have hJ't : IsUniqueInvolution (conjSub g K') (u * e) := hd.hgt ▸ hzK'.conj g
  have hJJ' : conjSub g K ≠ conjSub g K' := fun h => hs.hne (conjSub_injective g h).symm
  have hmem : ∀ M ∈ Ω, IsUniqueInvolution M (u * e) →
      conjSub x M = conjSub g K ∨ conjSub x M = conjSub g K' := by
    intro M hM hMt
    have h1 := hMt.conj x
    rw [ht] at h1
    exact hVt _ (hΩ.conjInvariant x M hM) h1
  have fJ : conjSub x (conjSub g K) = conjSub g K :=
    conjSub_eq_self_of_odd hodd hJJ' (hmem _ hJΩ hJt) (hmem _ hJ'Ω hJ't)
  have fJ' : conjSub x (conjSub g K') = conjSub g K' :=
    conjSub_eq_self_of_odd hodd hJJ'.symm (hmem _ hJ'Ω hJ't).symm (hmem _ hJΩ hJt).symm
  obtain ⟨R, R', a, b, r, hR, hR', -, hRN, hR'N, haR, hbR', -, -, hu, haa, hbb, -, -⟩ :=
    Q3T8.Asc77.T7K.exists_decomp hs hd
  have hKe : K ≤ Subgroup.centralizer ({e} : Set G) :=
    Q3T8.Asc77.T7Y.le_centralizer_e hs hd hα hKΩ hs.hz hR hRN
  have hK'e : K' ≤ Subgroup.centralizer ({e} : Set G) :=
    Q3T8.Asc77.T7Y.le_centralizer_e hs hd hα hK'Ω hzK' hR' hR'N
  have hJe := conjSub_le_centralizer_e3 hd hKe
  have hJ'e := conjSub_le_centralizer_e3 hd hK'e
  exact ⟨hxu, fun m hm => commute_of_inner hJe (hex _ hJΩ) hx fJ hm,
    fun m hm => commute_of_inner hJ'e (hex _ hJ'Ω) hx fJ' hm⟩

theorem oddCore_centralizer_u_eq_bot_of_thmE (hE : Q3T7E.ThmEWithSylow3)
    (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hd : Q3T8.Asc77.Hyp23bData Ω K K' W z u e g)
    (hex : ExactMembers Ω) (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) :
    classicalInvolutionOddCore ↥(Subgroup.centralizer ({u} : Set G)) = ⊥ := by
  classical
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hsup : Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) = ⊤ :=
    Q3T8.Asc77.T7Y.sup_centralizer_eq_top hE Q3T8.Asc77.c23_2_trans_proved hs hd
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ K ⊔ K' ⊔ Subgroup.centralizer ({u} : Set G) := by
    intro c hc
    obtain ⟨q, hq, c₀, hc₀, hcm, rfl⟩ :=
      Q3T8.Asc77.T7K.centralizer_eq_sup_mul hs hd.hu hd.hu1 hd.huz hd.hu2 hc
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hq)
      (Subgroup.mem_sup_right (Subgroup.mem_centralizer_singleton_iff.mpr hcm))
  have hGen : K ⊔ K' ⊔ Subgroup.centralizer ({u} : Set G) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hsup]
    exact sup_le le_sup_right hCz
  have hV : ∀ M ∈ Ω, IsUniqueInvolution M z → M = K ∨ M = K' := by
    intro M hM hMz
    have hmem : M ∈ twinSet Ω K := ⟨hM, z, hs.hz, hMz⟩
    rw [hs.twinSet_eq] at hmem
    exact hmem
  obtain ⟨R, R', a, b, r, hR, hR', -, hRN, hR'N, haR, hbR', -, -, hu, haa, hbb, -, -⟩ :=
    Q3T8.Asc77.T7K.exists_decomp hs hd
  have hMK : IsClassicalMember3 K z :=
    (Q3T8.Asc77.isClassicalMember_of_twin hΩ hKΩ hs.hz).toQ3 (by norm_num)
  have hMK' : IsClassicalMember3 K' z :=
    (Q3T8.Asc77.isClassicalMember_of_twin hΩ hK'Ω hzK').toQ3 (by norm_num)
  exact oddCore_centralizer_eq_bot_of_twins hΩ.conjInvariant hex hKΩ hK'Ω hs.hz hzK' hs.hne.symm
    hV (hR.1 haR) (hR'.1 hbR') haa hbb hu hd.hu1 (Q3T7S23.twins_commute_of_exact hs hex) hMK hMK'
    hα hGen

theorem layer_u_type_of_thmE (hE : Q3T7E.ThmEWithSylow3)
    (h : Q3T8.Asc77.Hyp23b Ω K K' W z u e g)
    (hEt : Q3T8.Asc77.LayerOrthType Ω e 6 (piSign 3 1)) :
    Q3T8.Asc77.LayerOrthType Ω u 5 true ∨ Q3T8.Asc77.LayerOrthType Ω u 6 (!piSign 3 1) := by
  rcases Q3T8.Asc77.c23_5X_type_proved G Ω K K' W z u e g h with hZ | h5 | h6
  · exact absurd hZ (Q3T8.Asc77.c23_9_noZX_of hE G Ω K K' W z u e g
      (Q3T8.Asc77.Hyp23.setting h.std) (Q3T8.Asc77.Hyp23b.data h) hEt)
  · exact Or.inl h5
  · exact Or.inr h6

end Frame

theorem oddCoreLayer23Neg3_of_thmE (hE : Q3T7E.ThmEWithSylow3) : Q3T7S23.OddCoreLayer23Neg3 := by
  intro G _ _ _ Ω K K' W z u e g h hα hEt
  classical
  have hs : Q3T8.Asc77.Hyp23Setting Ω K K' z := Q3T8.Asc77.Hyp23.setting h.std
  have hd : Q3T8.Asc77.Hyp23bData Ω K K' W z u e g := Q3T8.Asc77.Hyp23b.data h
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hex : ExactMembers Ω := exactMembers_of_alpha_23 hs hd hα.1
  have hOC := oddCore_centralizer_u_eq_bot_of_thmE hE hs hd hex hα.1
  have hOY : classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u) = ⊥ :=
    Q3T8.Asc77.ExactLayer.oddCore_exactLayer_eq_bot_of_centralizer hΩ.conjInvariant hOC
  have hYt := layer_u_type_of_thmE hE h hEt
  set E : Subgroup G := Q3T8.Asc77.ExactLayer.exactLayer Ω e with hEdef
  set N : Subgroup G := Balance.oddCoreIn E with hN
  have hNnorm : ∀ c ∈ Subgroup.centralizer ({e} : Set G), ∀ m ∈ N, c * m * c⁻¹ ∈ N := by
    intro c hc m hm
    have h1 : conjSub c E = E := Q3T8.Asc77.ExactLayer.conjSub_exactLayer hΩ.conjInvariant hc
    have h2 := Balance.Bootstrap.oddCoreIn_conjSub_eq c E
    rw [h1] at h2
    have h3 := conj_mem_conjSub (n := c) hm
    rwa [← h2] at h3
  have hNE : N ≤ E := Balance.oddCoreIn_le E
  have hNodd : Odd (Nat.card N) := Balance.odd_card_oddCoreIn E
  have hNle : N ≤ Balance.oddCoreIn (Subgroup.centralizer ({e} : Set G)) :=
    Balance.le_oddCoreIn_of_normalizes
      (hNE.trans (Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω e))
      (le_normalizer_of_conj_mem hNnorm) hNodd
  have hNY : ∀ n ∈ N, n ∈ Subgroup.centralizer ({u} : Set G) ∧
      ∀ y ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω u, n * y = y * n := by
    intro n hn
    obtain ⟨hxu, hJ, hJ'⟩ := oddCore_e_centralizes hs hd hα.1 hex (hNle hn)
    have hnu : n ∈ Subgroup.centralizer ({u} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hxu
    have hodd : Odd (orderOf n) := odd_orderOf_of_mem_oddCoreOf hn
    refine ⟨hnu, ?_⟩
    rcases hYt with h5 | h6
    · exact oddCentralizes_layer_sp hs hd hex hOY h5 hnu hodd hJ hJ'
    · exact oddCentralizes_layer_psl hs hd hex hOY h6 hnu hodd hJ hJ'
  have hNnormU : ∀ c ∈ Subgroup.centralizer ({u} : Set G), ∀ m ∈ N, c * m * c⁻¹ ∈ N := by
    intro c hc m hm
    obtain ⟨y, hy, c', hc', rfl⟩ := Q3T8.Asc77.T7Y.exists_mul_centralizer_u
      Q3T8.Asc77.twinCentralFact3_proved Q3T8.Asc77.e4TwinGen3_proved hs hd hc
    have hc'e : c' ∈ Subgroup.centralizer ({e} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (T7Y.comm_e_of_comm_u_ue hd.hu2 (Subgroup.mem_centralizer_singleton_iff.mp hc'.1)
          (Subgroup.mem_centralizer_singleton_iff.mp hc'.2))
    have h1 : c' * m * c'⁻¹ ∈ N := hNnorm c' hc'e m hm
    have h2 : y * (c' * m * c'⁻¹) * y⁻¹ = c' * m * c'⁻¹ := by
      have h3 := (hNY _ h1).2 y hy
      calc y * (c' * m * c'⁻¹) * y⁻¹ = ((c' * m * c'⁻¹) * y) * y⁻¹ := by rw [h3]
        _ = c' * m * c'⁻¹ := by group
    have h4 : (y * c') * m * (y * c')⁻¹ = c' * m * c'⁻¹ := by
      calc (y * c') * m * (y * c')⁻¹ = y * (c' * m * c'⁻¹) * y⁻¹ := by group
        _ = c' * m * c'⁻¹ := h2
    rw [h4]
    exact h1
  have hNu : N ≤ Balance.oddCoreIn (Subgroup.centralizer ({u} : Set G)) :=
    Balance.le_oddCoreIn_of_normalizes (fun n hn => (hNY n hn).1)
      (le_normalizer_of_conj_mem hNnormU) hNodd
  have h0 : Balance.oddCoreIn (Subgroup.centralizer ({u} : Set G)) = ⊥ := by
    show (classicalInvolutionOddCore ↥(Subgroup.centralizer ({u} : Set G))).map
      (Subgroup.centralizer ({u} : Set G)).subtype = ⊥
    rw [hOC, Subgroup.map_bot]
  have hNbot : N = ⊥ := le_bot_iff.mp (h0 ▸ hNu)
  have hinj : Function.Injective E.subtype := E.subtype_injective
  have hbot : (classicalInvolutionOddCore ↥E).map E.subtype = ⊥ := hNbot
  exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).mp hbot

end CFSG.ClassicalInvolution.Q3.Q3OCL
