module

public import CFSG.Certificates.Kernel.J4TreeTop.Node1EClass
public import CFSG.Certificates.Kernel.J4TreeTop.UneqSound
public import CFSG.Certificates.Kernel.J4TreeTop.LagrangeSound
public import CFSG.Milestones.ASVolI.C31.J4NP.TopNodeFacts

public section

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.J4TreeS CFSG.KC.F2W CFSG.J4Tree.Native CFSG.ASVolI
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
open CFSG.Quasithin.J4Loc (omegaZ)

@[expose] def TopTgt (k : ℕ) : Prop :=
  treeOrd k ≤ Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J)) ∧
    (Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J)) = treeOrd k →
      burnsideJ4NP_IsHCl (burnsideJ4NP_Rep k) (burnsideJ4NP_Rep k))

@[expose] def TopCover (A : Subgroup J) (ys : List J) : Prop :=
  ∀ x ∈ P0, x ∈ Subgroup.centralizer (A : Set J) → x * x = 1 → x ∉ A →
    (∃ n ∈ Hj, burnsideJ4NP_treeTest (burnsideJ4NP_encJ (n * x * n⁻¹)) = false) ∨
      ∃ y ∈ ys, ∃ n ∈ Hj, n ∈ Subgroup.normalizer (A : Set J) ∧ ∃ a ∈ A, n * x * n⁻¹ = y * a

theorem two_max_of_odd_index {G : Type*} [Group G] [Finite G] {K P : Subgroup G} (hPK : P ≤ K)
    {m : ℕ} (hK : Nat.card K = Nat.card P * m) (hm : m % 2 = 1) :
    ∀ Q : Subgroup G, Q ≤ K → IsPGroup 2 ↥Q → P ≤ Q → Q = P := by
  intro Q hQK hQ2 hPQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hQ2
  have hdvd : 2 ^ a ∣ Nat.card P * m := by
    rw [← ha, ← hK]
    exact Subgroup.card_dvd_of_le hQK
  have hcop : Nat.Coprime (2 ^ a) m :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hm))
  have h2 : 2 ^ a ≤ Nat.card P := Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_right hdvd)
  exact (Subgroup.eq_of_le_of_card_ge hPQ (by rw [ha]; exact h2)).symm

theorem isHCl_of_cent_eq {X Y B : Subgroup J}
    (he : Hj ⊓ Subgroup.centralizer (X : Set J) = Hj ⊓ Subgroup.centralizer (Y : Set J))
    (h : burnsideJ4NP_IsHCl X B) : burnsideJ4NP_IsHCl Y B := by
  obtain ⟨P, h1, h2, h3, h4⟩ := h
  rw [he] at h1 h3
  exact ⟨P, h1, h2, h3, h4⟩

theorem is2A_sq {x : J} (h : burnsideJ4NP_Is2A x) : x * x = 1 := by
  obtain ⟨g, rfl⟩ := h
  calc g * CFSG.Quasithin.J4Loc.z0 * g⁻¹ * (g * CFSG.Quasithin.J4Loc.z0 * g⁻¹)
      = g * (CFSG.Quasithin.J4Loc.z0 * CFSG.Quasithin.J4Loc.z0) * g⁻¹ := by group
    _ = 1 := by rw [burnsideJ4NP_z0_sq]; group

theorem merge_child {k k' : ℕ} {y : J} (hm : burnsideJ4NP_MergeFact k k' y) (ht : TopTgt k') :
    Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k' : Set J)) = treeOrd k' ∧
      ∃ h ∈ Hj, burnsideJ4NP_IsHCl (burnsideJ4NP_Rep k ⊔ Subgroup.zpowers y)
        ((burnsideJ4NP_Rep k').map (MulAut.conj h).toMonoidHom) := by
  obtain ⟨h, hh, hle, hcle⟩ := hm
  have e : Hj ⊓ Subgroup.centralizer
      (((burnsideJ4NP_Rep k').map (MulAut.conj h).toMonoidHom : Subgroup J) : Set J) =
      (Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k' : Set J)).map
        (MulAut.conj h).toMonoidHom := by
    rw [burnsideJ4NP_centralizer_map_conj, burnsideJ4NP_map_conj_inf,
      burnsideJ4NP_map_conj_of_mem hh]
  have hTle : Hj ⊓ Subgroup.centralizer
      (((burnsideJ4NP_Rep k').map (MulAut.conj h).toMonoidHom : Subgroup J) : Set J) ≤
      Hj ⊓ Subgroup.centralizer
        ((burnsideJ4NP_Rep k ⊔ Subgroup.zpowers y : Subgroup J) : Set J) :=
    inf_le_inf_left _ (Subgroup.centralizer_le hle)
  have hcT : Nat.card ↥(Hj ⊓ Subgroup.centralizer
      (((burnsideJ4NP_Rep k').map (MulAut.conj h).toMonoidHom : Subgroup J) : Set J)) =
      Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k' : Set J)) := by
    rw [e, burnsideJ4KW_card_map_conj]
  have h1 := Subgroup.card_le_of_le hTle
  have hc' : Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k' : Set J)) = treeOrd k' := by
    have := ht.1
    omega
  refine ⟨hc', h, hh, ?_⟩
  have heq := Subgroup.eq_of_le_of_card_ge hTle (by omega)
  exact isHCl_of_cent_eq heq (burnsideJ4NP_IsHCl_map_conj hh (ht.2 hc'))

theorem omegaZ_of_tgt {k : ℕ} (ht : TopTgt k) (h2 : ∃ n, treeOrd k = 2 ^ n)
    (hc : Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J)) = treeOrd k) :
    omegaZ (Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J)) = burnsideJ4NP_Rep k := by
  obtain ⟨n, hn⟩ := h2
  obtain ⟨P, hPK, -, hPmax, hPe⟩ := ht.2 hc
  have hC2 : IsPGroup 2 ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J)) :=
    IsPGroup.of_card (n := n) (by rw [hc, hn])
  rw [hPmax _ le_rfl hC2 hPK]
  exact hPe

theorem topUneq_pow2 {T : Tabs} {g : TGlob} {c : TUneq} {es : List (ℕ × ℕ × ℕ)}
    (h : topUneqOK T g c es = true) : ∃ n, treeOrd c.tgt = 2 ^ n := by
  unfold topUneqOK at h
  simp only [Bool.and_eq_true] at h
  exact pow2F_spec 64 _ h.1.1.2


theorem walk_topCover {T : Tabs} (hT : tabsOK T = true)
    (hsx : ∀ t < 2048, T.sx.testBit t = (burnsideJ4NP_sextArr ())[t]?.getD false) {k : ℕ}
    (hb : (treeBasis k).all coordOK = true) {H : WHd}
    (hH : whdOK T ((treeBasis k).map (ccT T)) H = true) {D R : ℕ → List ℕ}
    (hD : ∀ e < 1024, walkOK T ((treeBasis k).map (ccT T)) H e (D e) = true)
    {d : TopNode} {cg : CKGlob} (hg : ckGlobOK T ((treeBasis k).map (ccT T)) H d cg = true)
    (hR : ∀ e < 1024, coverKOK T ((treeBasis k).map (ccT T)) H cg e (D e) (R e) = true) :
    TopCover (burnsideJ4NP_Rep k) (d.children.map fun c => burnsideJ4NP_treeElt c.y) := by
  have hB2 : List.Forall₂ PK ((treeBasis k).map burnsideJ4NP_treeElt)
      ((treeBasis k).map (ccT T)) := forall₂_cc hT _ (List.all_eq_true.mp hb)
  have hAdef : burnsideJ4NP_Rep k = Acl ((treeBasis k).map burnsideJ4NP_treeElt) := rfl
  unfold TopCover
  rw [hAdef]
  generalize (treeBasis k).map burnsideJ4NP_treeElt = bJ at hB2 ⊢
  generalize (treeBasis k).map (ccT T) = B at hB2 hH hD hg hR
  obtain ⟨hbas, -⟩ := whd_spec hH
  obtain ⟨hsq', hcomm'⟩ := basis_props hB2 hbas
  intro x hxP hxC hsq hxA
  obtain ⟨e', he', Ki, ce, m, l, hDe, dd, -, hdC, I, -, hbit, y, a, hy, ha, hconj, -, -, -⟩ :=
    walk_cover_P0 hT hB2 hH hD hxP hxC hxA hsq
  have hRe := hR e' he'
  rw [hDe] at hRe
  have hdH : eta uJ 11 dd ∈ Hj := Eg_le_Hj (eta_mem_Eg 11 le_rfl dd)
  have ha' : a ∈ Subgroup.closure {g | g ∈ bJ} := ha
  have hav : ∃ v < 2 ^ bJ.length, a = nwFrom 1 bJ v := by
    refine mem_closure_nw ?_ ?_ ha'
    · intro p hp q hq
      exact hcomm' p hp q hq
    · intro p hp
      exact hsq' p hp
  obtain ⟨v, hv, rfl⟩ := hav
  rcases coverK_sound hT hsx hB2 hg hRe hbit hy with hnon | ⟨j, hj, n, hnH, hnN, w, -, hn⟩
  · left
    refine ⟨eta uJ 11 dd, hdH, ?_⟩
    rw [hconj]
    exact hnon v (by rw [← forall₂_length hB2]; exact hv)
  · right
    refine ⟨burnsideJ4NP_treeElt (d.children.getD j default).y, ?_, n * eta uJ 11 dd,
      Hj.mul_mem hnH hdH, ?_,
      nwFrom 1 bJ w * (n * nwFrom 1 bJ v * n⁻¹), ?_, ?_⟩
    · refine List.mem_map.mpr ⟨_, ?_, rfl⟩
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    · refine Subgroup.mul_mem _ hnN (mem_normalizer_of fun b hb' => ?_)
      have hc := mem_cen hdC (Subgroup.subset_closure hb')
      rw [← hc, mul_inv_cancel_right]
      exact Subgroup.subset_closure hb'
    · exact Subgroup.mul_mem _ (nwFrom_mem (fun b hb' => Subgroup.subset_closure hb')
        (Subgroup.one_mem _) w) ((Subgroup.mem_normalizer_iff.mp hnN _).mp ha)
    · calc n * eta uJ 11 dd * x * (n * eta uJ 11 dd)⁻¹
          = n * (eta uJ 11 dd * x * (eta uJ 11 dd)⁻¹) * n⁻¹ := by group
        _ = n * y * n⁻¹ * (n * nwFrom 1 bJ v * n⁻¹) := by
          rw [hconj]; group
        _ = _ := by rw [hn]; group

theorem node1_topCover {T : Tabs} (hT : tabsOK T = true)
    (hsx : ∀ t < 2048, T.sx.testBit t = (burnsideJ4NP_sextArr ())[t]?.getD false) {z : ℕ}
    (hz : coordOK (z, 0) = true) {g : C1Glob} (hg : c1GlobOK T z g = true) {D R : ℕ → List ℕ}
    (hD : ∀ e < 1024, eclassOK T z e (D e) = true)
    (hR : ∀ e < 1024, cover1OK T z e g (D e) (R e) = true) {k : ℕ}
    (hk : treeBasis k = [(z, 0)]) :
    TopCover (burnsideJ4NP_Rep k) (topNode1.children.map fun c => burnsideJ4NP_treeElt c.y) := by
  have hA : burnsideJ4NP_Rep k = Subgroup.closure {b | b ∈ [burnsideJ4NP_treeElt (z, 0)]} := by
    unfold burnsideJ4NP_Rep
    rw [hk]
    rfl
  have hzA : burnsideJ4NP_treeElt (z, 0) ∈ burnsideJ4NP_Rep k := by
    rw [hA]
    exact Subgroup.subset_closure (List.mem_singleton_self _)
  have hN : ∀ n ∈ Subgroup.centralizer {burnsideJ4NP_treeElt (z, 0)},
      n ∈ Subgroup.normalizer (burnsideJ4NP_Rep k : Set J) := by
    intro n hn
    rw [hA]
    refine mem_normalizer_of fun b hb => ?_
    rw [List.mem_singleton.mp hb]
    have hc := Subgroup.mem_centralizer_iff.mp hn (burnsideJ4NP_treeElt (z, 0))
      (Set.mem_singleton _)
    rw [← hc, mul_inv_cancel_right]
    exact Subgroup.subset_closure (List.mem_singleton_self _)
  unfold TopCover
  intro x hxP hxC hsq hxA
  have hxz : x ∈ Subgroup.centralizer {burnsideJ4NP_treeElt (z, 0)} :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]
      exact Subgroup.mem_centralizer_iff.mp hxC _ hzA
  have hx1 : x ≠ 1 := fun h1 => hxA (h1 ▸ Subgroup.one_mem _)
  have hxz1 : x ≠ burnsideJ4NP_treeElt (z, 0) := fun h1 => hxA (h1 ▸ hzA)
  rcases node1_cover hT hsx hz hg hD hR hxP hxz hsq hx1 hxz1 with
    ⟨n, hn, h1, -⟩ | ⟨j, hj, n, hn, h⟩
  · exact Or.inl ⟨n, (Subgroup.mem_inf.mp hn).1, h1⟩
  · right
    have hy : burnsideJ4NP_treeElt (topNode1.children.getD j default).y ∈
        topNode1.children.map fun c => burnsideJ4NP_treeElt c.y := by
      refine List.mem_map.mpr ⟨_, ?_, rfl⟩
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    obtain ⟨hnH, hnC⟩ := Subgroup.mem_inf.mp hn
    rcases h with h | h
    · exact ⟨_, hy, n, hnH, hN n hnC, 1, Subgroup.one_mem _, by rw [mul_one]; exact h⟩
    · exact ⟨_, hy, n, hnH, hN n hnC, _, hzA, h⟩

theorem foldr_lcm_dvd {M : ℕ} : ∀ l : List ℕ, (∀ x ∈ l, x ∣ M) → l.foldr Nat.lcm 1 ∣ M
  | [], _ => one_dvd M
  | a :: l, h => by
    rw [List.foldr_cons]
    exact Nat.lcm_dvd (h a List.mem_cons_self)
      (foldr_lcm_dvd l fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem topGlob_lower {T : Tabs} (hT : tabsOK T = true) (hq : Nat.beq (M QK QiK) oneK = true)
    {i : ℕ} {g : TGlob} (h : topGlobOK T i g = true) :
    treeOrd g.k ≤ Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J)) := by
  obtain ⟨-, -, -, -, -, -, hGC, hP0, h2n, hodd, hcop, hord⟩ := topGlob_sound hT hq h
  have hPC : Subgroup.closure {x | x ∈ g.cc.map burnsideJ4NP_treeElt} ≤
      Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J) :=
    (Subgroup.closure_le _).mpr fun s hs => hGC s (List.mem_append_right _ hs)
  have hP2 : IsPGroup 2 ↥(Subgroup.closure {x | x ∈ g.cc.map burnsideJ4NP_treeElt}) :=
    (CFSG.Quasithin.J4Loc.isPGroup_P0 j4Facts).to_le ((Subgroup.closure_le P0).mpr hP0)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP2
  have hna : g.cc.length ≤ a := by
    by_contra hlt
    have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (Nat.lt_of_not_le hlt)
    rw [← ha] at this
    omega
  have hOC : ∀ o ∈ g.odd, Subgroup.closure {x | x ∈ o.2.1.map fun j => (topGs g).getD j 1} ≤
      Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J) := by
    intro o _
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    by_cases hj : j < (topGs g).length
    · exact hGC _ (getD_mem hj)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Subgroup.one_mem _
  have hcop' : coprimeAll (2 ^ a :: g.odd.map Prod.fst) = true := by
    simp only [coprimeAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hcop ⊢
    refine ⟨fun b hb => ?_, hcop.2⟩
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hb
    exact Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (hodd o ho).2))
  have hdvd : (2 ^ a :: g.odd.map Prod.fst).foldr Nat.lcm 1 ∣
      Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J)) := by
    refine foldr_lcm_dvd _ fun x hx => ?_
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [← ha]
      exact Subgroup.card_dvd_of_le hPC
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
      rw [← (hodd o ho).1]
      exact Subgroup.card_dvd_of_le (hOC o ho)
  rw [foldr_lcm_eq_prod _ hcop', List.foldr_cons] at hdvd
  calc treeOrd g.k = 2 ^ g.cc.length * (g.odd.map Prod.fst).foldr (· * ·) 1 := hord
    _ ≤ 2 ^ a * (g.odd.map Prod.fst).foldr (· * ·) 1 :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hna)
    _ ≤ _ := Nat.le_of_dvd Nat.card_pos hdvd

theorem walk_topTgt {T : Tabs} (hT : tabsOK T = true) (hq : Nat.beq (M QK QiK) oneK = true)
    {i : ℕ} {g : TGlob} (hg : topGlobOK T i g = true) {H : WHd}
    (hH : whdOK T ((treeBasis g.k).map (ccT T)) H = true) {D : ℕ → List ℕ}
    (hD : ∀ e < 1024, walkOK T ((treeBasis g.k).map (ccT T)) H e (D e) = true) :
    TopTgt g.k := by
  refine ⟨topGlob_lower hT hq hg, fun hN => ?_⟩
  obtain ⟨-, -, -, -, -, -, hGC, hP0, -, hodd, -, hord⟩ := topGlob_sound hT hq hg
  obtain ⟨-, hP2, hPcard⟩ := topGlob_lagrange hT hq hg hN
  have hb : (treeBasis g.k).all coordOK = true := by
    have hg' := hg
    unfold topGlobOK at hg'
    simp only [Bool.and_eq_true] at hg'
    exact hg'.1.1.1.1.1.1.1.1.1.1.1.2
  have hB2 : List.Forall₂ PK ((treeBasis g.k).map burnsideJ4NP_treeElt)
      ((treeBasis g.k).map (ccT T)) := forall₂_cc hT _ (List.all_eq_true.mp hb)
  have hAP0 : ∀ b ∈ (treeBasis g.k).map burnsideJ4NP_treeElt, b ∈ P0 := by
    intro b hb'
    obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp hb'
    have hc := List.all_eq_true.mp hb ce hce
    unfold coordOK at hc
    rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at hc
    exact burnsideJ4NP_treeElt_mem_P0 hc.2
  have hgs : ∀ s ∈ H.gs.map burnsideJ4NP_treeElt,
      s ∈ P0 ∧ s ∈ Ccl ((treeBasis g.k).map burnsideJ4NP_treeElt) := by
    have hH' := hH
    unfold whdOK at hH'
    simp only [Bool.and_eq_true, List.all_eq_true] at hH'
    intro s hs
    obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp hs
    have hc := hH'.1.2 ce hce
    refine ⟨?_, cen_of_pk hB2 (pk_cc hT hc) (hH'.2 _ (List.mem_map.mpr ⟨ce, hce, rfl⟩))⟩
    unfold coordOK at hc
    rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at hc
    exact burnsideJ4NP_treeElt_mem_P0 hc.2
  obtain ⟨hbas, -⟩ := whd_spec hH
  have hPC : Subgroup.closure {x | x ∈ g.cc.map burnsideJ4NP_treeElt} ≤
      Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J) :=
    (Subgroup.closure_le _).mpr fun s hs => hGC s (List.mem_append_right _ hs)
  have hprod : (g.odd.map Prod.fst).foldr (· * ·) 1 % 2 = 1 := foldr_mul_odd _ fun x hx => by
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
    exact (hodd o ho).2
  have hPmax := two_max_of_odd_index hPC (m := (g.odd.map Prod.fst).foldr (· * ·) 1)
    (by rw [hN, hord, hPcard]) hprod
  have hQ : P0 ⊓ (Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J)) =
      Subgroup.closure {x | x ∈ g.cc.map burnsideJ4NP_treeElt} :=
    hPmax _ inf_le_right ((CFSG.Quasithin.J4Loc.isPGroup_P0 j4Facts).to_le inf_le_left)
      (le_inf ((Subgroup.closure_le P0).mpr hP0) hPC)
  have hmemP : ∀ x ∈ P0, x ∈ Hj → x ∈ Ccl ((treeBasis g.k).map burnsideJ4NP_treeElt) →
      x ∈ Subgroup.closure {x | x ∈ g.cc.map burnsideJ4NP_treeElt} := by
    intro x h1 h2 h3
    rw [← hQ]
    exact Subgroup.mem_inf.mpr ⟨h1, Subgroup.mem_inf.mpr ⟨h2, h3⟩⟩
  refine ⟨_, hPC, hP2, hPmax, le_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨hxP, hxc, hxx⟩ := CFSG.Quasithin.J4Loc.mem_omegaZ.mp hx
    by_contra hxA
    have hxP0 : x ∈ P0 := (Subgroup.closure_le P0).mpr hP0 hxP
    have hxC : x ∈ Ccl ((treeBasis g.k).map burnsideJ4NP_treeElt) :=
      (Subgroup.mem_inf.mp (hPC hxP)).2
    obtain ⟨-, -, -, -, -, -, -, dd, -, hdC, -, -, -, y, a, -, ha, hconj, -, -, s, hs, hsy⟩ :=
      walk_cover_P0 hT hB2 hH hD hxP0 hxC hxA hxx
    have hd0 : eta uJ 11 dd ∈ P0 := by
      have := burnsideJ4NP_treeElt_mem_P0 (ce := (dd, 0)) (by norm_num)
      rwa [treeElt_z0] at this
    have hdP := hmemP _ hd0 (Eg_le_Hj (eta_mem_Eg 11 le_rfl dd)) hdC
    have hxd : eta uJ 11 dd * x * (eta uJ 11 dd)⁻¹ = x := by
      rw [← hxc _ hdP, mul_inv_cancel_right]
    rw [hxd] at hconj
    obtain ⟨hs0, hsC⟩ := hgs s hs
    have hsP := hmemP s hs0 (P0_le_Hj hs0) hsC
    have h1 := hxc s hsP
    have h2 := mem_cen hsC ha
    have h3 : s * a⁻¹ = a⁻¹ * s := by
      calc s * a⁻¹ = a⁻¹ * (a * s) * a⁻¹ := by group
        _ = a⁻¹ * (s * a) * a⁻¹ := by rw [h2]
        _ = a⁻¹ * s := by group
    have hy : y = x * a⁻¹ := by rw [hconj]; group
    apply hsy
    rw [hy]
    calc s * (x * a⁻¹) = s * x * a⁻¹ := by group
      _ = x * s * a⁻¹ := by rw [h1]
      _ = x * (s * a⁻¹) := by group
      _ = x * (a⁻¹ * s) := by rw [h3]
      _ = x * a⁻¹ * s := by group
  · have hAP : burnsideJ4NP_Rep g.k ≤ Subgroup.closure {x | x ∈ g.cc.map burnsideJ4NP_treeElt} := by
      rw [← hQ]
      exact le_inf ((Subgroup.closure_le P0).mpr hAP0)
        (le_inf ((Subgroup.closure_le Hj).mpr (mem_Hj_of hB2)) (acl_le_ccl hB2 hbas))
    intro a ha
    exact CFSG.Quasithin.J4Loc.mem_omegaZ.mpr ⟨hAP ha, fun y hy => mem_cen (Subgroup.mem_inf.mp
      (hPC hy)).2 ha, acl_sq hB2 hbas ha⟩

theorem topNode_facts (haff : burnsideJ4NP_Aff2A) {T : Tabs} (hT : tabsOK T = true)
    (hq : Nat.beq (M QK QiK) oneK = true)
    {i : ℕ} {d : TopNode} (hd : topNodes.getD i default = d) {g : TGlob}
    (hg : topGlobOK T i g = true)
    (hch : ∀ j < d.children.length,
      (∃ c : TMerge, ∃ es, c.i = i ∧ c.j = j ∧ topMergeOK T g c es = true) ∨
      (∃ c : TUneq, ∃ es, c.i = i ∧ c.j = j ∧ topUneqOK T g c es = true) ∨
      (∃ c : TUneq, ∃ es, c.i = i ∧ c.j = j ∧ topPruneOK T g c es = true))
    (htgt : ∀ j < d.children.length, (d.children.getD j default).target ≠ 0 →
      TopTgt (d.children.getD j default).target)
    (hcov : TopCover (burnsideJ4NP_Rep d.node) (d.children.map fun c => burnsideJ4NP_treeElt c.y))
    (hN : Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep d.node : Set J)) =
      treeOrd d.node) :
    burnsideJ4NP_TreeStep d.node ∧
      ∀ kd ∈ d.kids, Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep kd.1 : Set J)) =
        treeOrd kd.1 := by
  obtain ⟨hk, hkids, hkd, -, hG, hGI, hGC, hP0, -, hodd, -, hord⟩ := topGlob_sound hT hq hg
  rw [hd] at hk hkids hkd
  rw [← hk] at hN hcov ⊢
  obtain ⟨-, hP2, hPcard⟩ := topGlob_lagrange hT hq hg hN
  unfold TopCover at hcov
  have hPC : Subgroup.closure {x | x ∈ g.cc.map burnsideJ4NP_treeElt} ≤
      Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep g.k : Set J) :=
    (Subgroup.closure_le _).mpr fun s hs => hGC s (List.mem_append_right _ hs)
  have hprod : (g.odd.map Prod.fst).foldr (· * ·) 1 % 2 = 1 := foldr_mul_odd _ fun x hx => by
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
    exact (hodd o ho).2
  have hPmax := two_max_of_odd_index hPC (m := (g.odd.map Prod.fst).foldr (· * ·) 1)
    (by rw [hN, hord, hPcard]) hprod
  have hcover := burnsideJ4NP_cover_of_sylow (d.children.map fun c => burnsideJ4NP_treeElt c.y)
    hPC hP2 hPmax fun x hxP h2A hxA => by
      have hxC := hPC hxP
      have hxH := (Subgroup.mem_inf.mp hxC).1
      have hxP0 : x ∈ P0 := (Subgroup.closure_le P0).mpr hP0 hxP
      have hne : x ≠ 1 := fun h1 => hxA (h1 ▸ Subgroup.one_mem _)
      rcases hcov x hxP0 (Subgroup.mem_inf.mp hxC).2 (is2A_sq h2A) hxA with
        ⟨n, hn, hf⟩ | ⟨y, hy, n, hnH, hnN, a, ha, he⟩
      · exfalso
        have hne' : n * x * n⁻¹ ≠ 1 := fun h1 => hne (by
          have e : x = n⁻¹ * (n * x * n⁻¹) * n := by group
          rw [e, h1]
          group)
        rw [haff _ (Hj.mul_mem (Hj.mul_mem hn hxH) (Hj.inv_mem hn)) hne'
          ((burnsideJ4NP_Is2A_conj n).mpr h2A)] at hf
        exact Bool.noConfusion hf
      · exact ⟨y, hy, n⁻¹, Hj.inv_mem hnH, coverK_sup hnN ha he⟩
  have hchildj : ∀ j < d.children.length, ∃ B₀ : Subgroup J,
      burnsideJ4NP_IsHCl (burnsideJ4NP_Rep g.k ⊔
        Subgroup.zpowers (burnsideJ4NP_treeElt (d.children.getD j default).y)) B₀ ∧
      (2 ^ 10 < Nat.card ↥B₀ ∨ 2 ^ 6 < Nat.card ↥(B₀ ⊓ Eg uJ 11) ∨
        ∃ k' < treeN, ∃ h ∈ Hj, B₀ =
          ((fun k' => burnsideJ4NP_Rep (k' + 1)) k').map (MulAut.conj h).toMonoidHom) := by
    intro j hj
    rcases hch j hj with ⟨c, es, hci, hcj, hc⟩ | ⟨c, es, hci, hcj, hc⟩ | ⟨c, es, hci, hcj, hc⟩
    · obtain ⟨-, -, hy, htg, h1, h2, -, -, hmf⟩ := topMerge_sound hT hc hG hGI hGC
      rw [hci, hd, hcj] at hy htg
      have ht := htgt j hj (by rw [← htg]; omega)
      rw [← htg] at ht
      obtain ⟨-, h, hh, hcl⟩ := merge_child (hmf hN) ht
      rw [← hy]
      refine ⟨_, hcl, Or.inr (Or.inr ⟨c.tgt - 1, by omega, h, hh, ?_⟩)⟩
      simp only [Nat.sub_add_cancel h1]
    · obtain ⟨-, -, hy, htg, h1, h2, -, -, hu⟩ := topUneq_sound hT hc hG hGI hGC
      rw [hci, hd, hcj] at hy htg
      have ht := htgt j hj (by rw [← htg]; omega)
      rw [← htg] at ht
      obtain ⟨hle, hcl⟩ := hu hN
      have hcard := le_antisymm hle ht.1
      obtain ⟨h, hh, hB⟩ := hcl ht.1 (omegaZ_of_tgt ht (topUneq_pow2 hc) hcard)
      rw [← hy]
      refine ⟨_, hB, Or.inr (Or.inr ⟨c.tgt - 1, by omega, h, hh, ?_⟩)⟩
      simp only [Nat.sub_add_cancel h1]
    · obtain ⟨-, -, hy, -, -, -, -, hpr⟩ := topPrune_sound hT hq hc hG hGI hGC
      rw [hci, hd, hcj] at hy
      obtain ⟨B₀, hB, hBE⟩ := hpr hN
      rw [← hy]
      exact ⟨B₀, hB, Or.inr (Or.inl hBE)⟩
  have hchild : ∀ y ∈ d.children.map (fun c => burnsideJ4NP_treeElt c.y), ∃ B₀ : Subgroup J,
      burnsideJ4NP_IsHCl (burnsideJ4NP_Rep g.k ⊔ Subgroup.zpowers y) B₀ ∧
      (2 ^ 10 < Nat.card ↥B₀ ∨ 2 ^ 6 < Nat.card ↥(B₀ ⊓ Eg uJ 11) ∨
        ∃ k' < treeN, ∃ h ∈ Hj, B₀ =
          ((fun k' => burnsideJ4NP_Rep (k' + 1)) k').map (MulAut.conj h).toMonoidHom) := by
    intro y hy
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hy
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc0
    have := hchildj j hj
    rwa [List.getD_eq_getElem _ _ hj] at this
  refine ⟨?_, fun kd hkd' => ?_⟩
  · intro x hx h2A hxA B hB hB10 hBE
    obtain ⟨k', hk', h', hh', e⟩ := burnsideJ4NP_step_of_children
      (fun j => burnsideJ4NP_Rep (j + 1)) treeN _ hcover hchild x hx h2A hxA B hB hB10 hBE
    exact ⟨k' + 1, by omega, by omega, h', hh', e⟩
  ·
    obtain ⟨hj, htg0, hne0⟩ := hkd kd (by rw [hkids]; exact hkd')
    have ht := htgt kd.2 hj (by rw [htg0]; exact hne0)
    rw [htg0] at ht
    rcases hch kd.2 hj with ⟨c, es, hci, hcj, hc⟩ | ⟨c, es, hci, hcj, hc⟩ | ⟨c, es, hci, hcj, hc⟩
    · obtain ⟨-, -, -, htg, -, -, -, -, hmf⟩ := topMerge_sound hT hc hG hGI hGC
      rw [hci, hd, hcj, htg0] at htg
      rw [← htg] at ht ⊢
      exact (merge_child (hmf hN) ht).1
    · obtain ⟨-, -, -, htg, -, -, -, -, hu⟩ := topUneq_sound hT hc hG hGI hGC
      rw [hci, hd, hcj, htg0] at htg
      rw [← htg] at ht ⊢
      exact le_antisymm (hu hN).1 ht.1
    · obtain ⟨-, -, -, htg, h0, -, -, -⟩ := topPrune_sound hT hq hc hG hGI hGC
      rw [hci, hd, hcj, htg0] at htg
      exact absurd (htg.symm.trans h0) hne0

end CFSG.KC.J4TreeT
