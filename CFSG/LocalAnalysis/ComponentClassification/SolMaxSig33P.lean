module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33O

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

namespace Sol33

variable {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {y : X} (S : Sol33 X t J n θ E D y)
include S

theorem dagger (hbal : Sol78.BalanceTwoComponentInput) (hPO : S.PumpOracle) {a b : X}
    (ha : a ∈ E ⊔ zpowers y) (ha1 : a ≠ 1)
    (hb : b ∈ E ⊔ zpowers y) (hb1 : b ≠ 1) {L : Subgroup X}
    (hLC : L ≤ centralizer ({b} : Set X))
    (hLpc : IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set X))))
    (hLX : ¬ ⁅L, (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
        (centralizer ({a} : Set X)).subtype ⊓ centralizer ({b} : Set X)⁆ ≤
      (pPrimeCore 2 ↥(centralizer ({b} : Set X))).map (centralizer ({b} : Set X)).subtype) :
    E ≤ UnbalancedLayer.coreActionKernel L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb2 := S.mul_self_of_mem hb
  have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hb2) hb1
  have htb := S.t_comm hb
  have : IsElementaryAbelian 2 ↥(E ⊔ zpowers y) := S.elementary
  have hB2 : IsPGroup 2 ↥(E ⊔ zpowers y) := IsElementaryAbelian.isPGroup 2 ↥(E ⊔ zpowers y)
  obtain ⟨f, hfJ, hfB, hfo, hfs4, hfD⟩ :=
    exists_involution_centralizer_disjoint θ (by have := S.pair.2.2.1; omega) S.le S.card S.supp
      S.hyK hB2
  set Cf : Subgroup X := centralizer ({f} : Set X) with hCfdef
  set Of := (pPrimeCore 2 ↥Cf).map Cf.subtype with hOfdef
  set Oa := (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
    (centralizer ({a} : Set X)).subtype with hOadef
  have hf2 : f * f = 1 := by rw [← sq, ← hfo, pow_orderOf_eq_one]
  have hfb : f * b = b * f := (mem_centralizer_iff.mp hfB b hb).symm
  have hbCf : b ∈ Cf := mem_centralizer_singleton_iff.mpr hfb.symm
  have htf : t * f = f * t := (mem_centralizer_singleton_iff.mp (S.pair.1.2.1 hfJ)).symm
  have htCf : t ∈ Cf := mem_centralizer_singleton_iff.mpr htf
  obtain ⟨Lf, hLfL, hLfC, hLfpc, hLfsup, hcoreL, hLfX⟩ :=
    S.exists_fixedLayer_unbalanced hbal hPO ha ha1 hb hb1 hLC hLpc hLX hfJ hfB hfo hfD
  have hEf : ∀ (e : X) (he : e ∈ E),
      (coreImage θ (S.le he)).support ⊆ (coreImage θ hfJ).supportᶜ := by
    intro e he z hz
    rw [Finset.mem_compl]
    intro hz'
    exact Finset.disjoint_left.mp hfD hz' (S.supp e (S.le he) he hz)
  have hτc : ∀ (e : X) (he : e ∈ E), coreImage θ (S.le he) * coreImage θ hfJ =
      coreImage θ hfJ * coreImage θ (S.le he) := by
    intro e he
    have hd : (coreImage θ (S.le he)).Disjoint (coreImage θ hfJ) := by
      rw [Perm.disjoint_iff_disjoint_support]
      exact Finset.disjoint_of_subset_left (hEf e he) disjoint_compl_left
    exact hd.commute.eq
  have hcef : f * f⁻¹ ∈ UnbalancedLayer.coreActionKernel J := by
    rw [mul_inv_cancel]
    exact one_mem _
  obtain ⟨Jf, Mf, -, hinvf, hMfC, hMfpc, hJfM, hJfK, hJfN, hbalf⟩ :=
    hPO hfB htf (le_normalizer hfJ) hfo hfJ hf2 hcef hfs4 hτc (Or.inr hEf)
  obtain ⟨hMftC, hMftpc⟩ := isPComponent_conj hMfC hMfpc htCf
  obtain ⟨e₁, he₁, hce₁⟩ := S.exists_acts_like_E hb
  have hbJf : b ∈ normalizer (Jf : Set X) := by
    refine hJfN b (S.mem_normalizer hb) hfb.symm fun x hx hxs => ?_
    have hbx := (mem_normalizer_iff.mp (S.mem_normalizer hb) x).mp hx
    rw [coreImage_conj_of_acts θ (S.le he₁) hce₁ hx hbx]
    exact support_conj_subset_compl (hτc e₁ he₁) hxs
  have hpair := map_conj_mem_pair S.t_mul_self htCf hbCf htb hMfC hMfpc hJfM hbJf hJfK
  set Mft := Mf.map (MulAut.conj t).toMonoidHom with hMftdef
  have hcommtb : ∀ K : Subgroup X, (K.map (MulAut.conj t).toMonoidHom).map
      (MulAut.conj b).toMonoidHom =
        (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
    intro K
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext z
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply]
    calc b * (t * z * t⁻¹) * b⁻¹ = (b * t) * z * (b * t)⁻¹ := by group
      _ = (t * b) * z * (t * b)⁻¹ := by rw [htb]
      _ = t * (b * z * b⁻¹) * t⁻¹ := by group
  have hpairb : ∀ N : Subgroup X, (N = Mf ∨ N = Mft) →
      (N.map (MulAut.conj b).toMonoidHom = Mf ∨ N.map (MulAut.conj b).toMonoidHom = Mft) := by
    rintro N (rfl | rfl)
    · exact hpair
    · rw [hMftdef, hcommtb]
      rcases hpair with h | h
      · rw [h]
        exact Or.inr rfl
      · rw [h, map_conj_map_conj_of_mul_self S.t_mul_self]
        exact Or.inl rfl
  have hbb : ∀ N : Subgroup X, (N.map (MulAut.conj b).toMonoidHom).map
      (MulAut.conj b).toMonoidHom = N := fun N => map_conj_map_conj_of_mul_self hb2 N
  have hLfC' : Lf ≤ Cf ⊓ centralizer ({b} : Set X) := by
    rw [inf_comm]
    exact hLfC
  have hLfpc' : IsPComponent 2 (Lf.subgroupOf (Cf ⊓ centralizer ({b} : Set X))) := by
    rw [inf_comm]
    exact hLfpc
  obtain ⟨N, hNC, hNpc, hLfN⟩ := orbit_location_in hbCf hbo hLfC' hLfpc'
  set Nb := N.map (MulAut.conj b).toMonoidHom with hNbdef
  obtain ⟨hNbC, hNbpc⟩ := isPComponent_conj hNC hNpc hbCf
  have hCfN : Cf ≤ normalizer (Of : Set X) := Sol78.le_normalizer_map_subtype (pPrimeCore 2 ↥Cf)
  have hXfle : (Oa ⊓ centralizer ({b} : Set X)) ⊓ Cf ≤ Oa ⊓ Cf :=
    inf_le_inf_right _ inf_le_left
  have hbalpair : ∀ K : Subgroup X, (K = Mf ∨ K = Mft) →
      ⁅(Oa ⊓ centralizer ({b} : Set X)) ⊓ Cf, K⁆ ≤ Of := by
    rintro K (rfl | rfl)
    · rw [commutator_comm]
      exact (commutator_mono le_rfl hXfle).trans (hbalf a ha ha1).1
    · rw [commutator_comm]
      exact (commutator_mono le_rfl hXfle).trans (hbalf a ha ha1).2
  have hNnot : ¬ (N = Mf ∨ N = Mft) := by
    intro hN
    have hNb := hpairb N hN
    apply hLfX
    rw [commutator_comm]
    refine (commutator_mono le_rfl hLfN).trans ?_
    exact commutator_sup_le hCfN hNC hNbC (hbalpair N hN) (hbalpair Nb hNb)
  have hNbnot : ¬ (Nb = Mf ∨ Nb = Mft) := by
    intro hNb
    apply hNnot
    have h1 := hpairb Nb hNb
    rwa [hNbdef, hbb] at h1
  have hEJf : ∀ e ∈ E, e ∈ Jf := fun e he =>
    hinvf e (S.le he) (mem_centralizer_iff.mp hfB e (mem_sup_left he))
      ⟨1, by rw [pow_one, sq]; exact S.mul_self_of_mem_E he⟩ (hEf e he)
  have hEK : ∀ K : Subgroup X, K ≤ Cf → IsPComponent 2 (K.subgroupOf Cf) →
      ¬ (K = Mf ∨ K = Mft) → E ≤ UnbalancedLayer.coreActionKernel K := by
    intro K hKC hKpc hK e he
    push Not at hK
    have h1 := GSThmB.B5a.le_coreActionKernel_of_ne hKC hMfC hKpc hMfpc hK.1
    have h2 := GSThmB.B5a.le_coreActionKernel_of_ne hKC hMftC hKpc hMftpc hK.2
    exact (sup_le h1 h2) (hJfM (hEJf e he))
  have hEN := hEK N hNC hNpc hNnot
  have hENb := hEK Nb hNbC hNbpc hNbnot
  have hNNb : N ≤ normalizer (Nb : Set X) := by
    by_cases h : Nb = N
    · rw [h]
      exact le_normalizer
    · exact fun z hz => (GSThmB.B5a.le_coreActionKernel_of_ne hNbC hNC hNbpc hNpc h hz).1
  have hNbN : Nb ≤ normalizer (N : Set X) := by
    by_cases h : Nb = N
    · rw [h]
      exact le_normalizer
    · exact fun z hz => (GSThmB.B5a.le_coreActionKernel_of_ne hNC hNbC hNpc hNbpc
        (Ne.symm h) hz).1
  have hONf : (pPrimeCore 2 ↥N).map N.subtype ⊔ (pPrimeCore 2 ↥Nb).map Nb.subtype ≤ Of :=
    sup_le (pPrimeCore_le_of_isPComponent hNC hNpc) (pPrimeCore_le_of_isPComponent hNbC hNbpc)
  have hH : Of ⊓ centralizer ({b} : Set X) ≤
      (pPrimeCore 2 ↥(centralizer ({b} : Set X) ⊓ Cf)).map
        (centralizer ({b} : Set X) ⊓ Cf).subtype := by
    refine le_pPrimeCore_map (le_inf inf_le_right (inf_le_left.trans (map_subtype_le _))) ?_ ?_
    · intro g hg
      exact inf_mem_normalizer' (hCfN hg.2) (le_normalizer hg.1)
    · have h1 : Nat.card ↥(Of ⊓ centralizer ({b} : Set X)) ∣ Nat.card Of :=
        card_dvd_of_le inf_le_left
      rw [hOfdef, card_map_of_injective Cf.subtype_injective] at h1
      exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  have hLfperf : ⁅Lf, Lf⁆ = Lf := UnbalancedCorr.commutator_eq_of_isPComponent hLfC hLfpc
  have hLfq : Nontrivial (↥Lf ⧸ pPrimeCore 2 ↥Lf) :=
    LocalCores.isQuasisimple_nontrivial
      ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 Lf _ hLfC).mp hLfpc).2.2
  intro e he
  have heB : e ∈ E ⊔ zpowers y := mem_sup_left he
  have heb : e ∈ centralizer ({b} : Set X) :=
    mem_centralizer_singleton_iff.mpr (S.comm_of_mem heB hb)
  have hef : e ∈ Cf := mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hfB e heB)
  have hQ : ∀ x ∈ Lf, x⁻¹ * e⁻¹ * x * e ∈ (pPrimeCore 2 ↥(centralizer ({b} : Set X) ⊓ Cf)).map
      (centralizer ({b} : Set X) ⊓ Cf).subtype := by
    intro x hx
    have h1 := commutator_mem_sup_core hNNb hNbN (hEN he) (hENb he) (hLfN hx)
    refine hH (Subgroup.mem_inf.mpr ⟨hONf h1, ?_⟩)
    have hxb : x ∈ centralizer ({b} : Set X) := (hLfC hx).1
    exact mul_mem (mul_mem (mul_mem (inv_mem hxb) (inv_mem heb)) hxb) heb
  have heLf := mem_coreActionKernel_of_mod_core hLfC hLfpc ⟨heb, hef⟩
    (S.mul_self_of_mem_E he) hQ
  exact mem_coreActionKernel_of_fixedLayer hLC hLpc hLfL hLfperf hLfq hLfsup hcoreL heb heLf

end Sol33

end CFSG.ComponentClassification.SolMax
