module

public import CFSG.Quasithin.Background.DicksonPerfectPSL2
public import CFSG.Dihedral.Glauberman.DicksonMaxList
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality
public import Mathlib.GroupTheory.SpecificGroups.ZGroup

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open CFSG.BenderSuzuki.MatrixGroups CFSG.Glauberman.Dickson CFSG.GorensteinWalter
  CFSG.Quasithin.Dickson


theorem psl2_eq_top_of_orderOf_six {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p ^ f) (hq : 120 ≤ p ^ f) (H : Subgroup (PSL2MatrixGroup F))
    (hns : ¬ Group.IsSolvable H) {n : ℕ} (hn : ¬ n ∣ 60) (hnq : n ∣ p ^ f + 1)
    (hnq2 : p ^ f + 1 ≤ 6 * n) (hx : ∃ x ∈ H, orderOf x = n) : H = ⊤ := by
  obtain ⟨x, hxH, hxn⟩ := hx
  have hp := (Fact.out : p.Prime)
  have hf0 : f ≠ 0 := CFSG.BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have hcop : Nat.Coprime n p := by
    have h1 : Nat.Coprime (p ^ f + 1) p := by
      refine Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr fun hd => ?_)
      have := (Nat.dvd_add_right (dvd_pow_self p hf0)).mp hd
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    exact h1.coprime_dvd_left hnq
  have hxH' : orderOf (⟨x, hxH⟩ : H) = n := by
    rw [← hxn]; exact (orderOf_submonoid ⟨x, hxH⟩).symm
  have hdvdH : n ∣ Nat.card H := hxn ▸ Subgroup.orderOf_dvd_natCard H hxH
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification hF H with
    h1 | ⟨z, -, -, hcyc⟩ | ⟨z, -, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, -, -, N, C, hN, hNel, -, hC, -, -, hsup⟩ | ⟨m, hm, hmf, ⟨e⟩⟩ | ⟨m, hm, hmf, ⟨e⟩⟩
  · have := h1.toIsMulCommutative
    exact absurd (inferInstance : Group.IsSolvable H) hns
  · exact absurd (inferInstance : Group.IsSolvable H) hns
  · have := isSolvable_dihedral z
    exact absurd (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective) hns
  · have := alternatingGroup.isSolvable (α := Fin 4) (by simp)
    exact absurd (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective) hns
  · have := Equiv.Perm.isSolvable (α := Fin 4) (by simp)
    exact absurd (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective) hns
  · exfalso
    rw [Nat.card_congr e.toEquiv, card_alt_five] at hdvdH
    exact hn hdvdH
  · exfalso
    apply hns
    have := hN
    have hcomm : commutator H ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    have hNs : Group.IsSolvable N := by
      have := hNel.toIsMulCommutative
      infer_instance
    have hQs : Group.IsSolvable (H ⧸ N) := by
      have : IsMulCommutative (H ⧸ N) :=
        Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
      infer_instance
    exact Group.isSolvable_of_subgroup_quotient N
  ·
    have hcardm : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
    have hmf' : m ≤ f := Nat.le_of_dvd (Nat.pos_of_ne_zero hf0) hmf
    have hord : orderOf (e ⟨x, hxH⟩) = n := by rw [MulEquiv.orderOf_eq]; exact hxH'
    have psl_tail : n ≤ p ^ m + 1 → H = ⊤ := by
      intro hnle
      rcases Nat.lt_or_ge m f with hlt | hge
      · exfalso
        obtain ⟨k, hk⟩ := hmf
        have hk2 : 2 ≤ k := by
          rcases k with _ | _ | k
          · omega
          · omega
          · omega
        have h2m : 2 * m ≤ f := by rw [hk]; nlinarith
        have hsq : (p ^ m) * (p ^ m) ≤ p ^ f := by
          rw [← pow_add]; exact Nat.pow_le_pow_right hp.pos (by omega)
        have h6 : p ^ m ≤ 6 := by
          by_contra hc
          have hc := not_le.mp hc
          nlinarith
        linarith
      · have hmeq : m = f := le_antisymm hmf' hge
        subst hmeq
        have hcardF : Nat.card (GaloisField p m) = Nat.card F := by rw [hcardm, hF]
        let : Fintype F := Fintype.ofFinite F
        let : Fintype (GaloisField p m) := Fintype.ofFinite _
        have hcardF' : Fintype.card (GaloisField p m) = Fintype.card F := by
          rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
          exact hcardF
        have eF : GaloisField p m ≃+* F := FiniteField.ringEquivOfCardEq hcardF'
        apply Subgroup.eq_top_of_card_eq
        rw [Nat.card_congr e.toEquiv]
        exact Nat.card_congr (h826_pslEquiv eF).toEquiv
    rcases psl2_orderOf_dvd hcardm (e ⟨x, hxH⟩) with h | h | h
    · exfalso
      rw [hord] at h
      have := (Nat.coprime_comm.mp hcop)
      have h1 : n = 1 := Nat.Coprime.eq_one_of_dvd hcop h
      exact hn (h1 ▸ one_dvd _)
    · have hm1 : 1 < p ^ m := Nat.one_lt_pow hm hp.one_lt
      have hg : Nat.gcd (p ^ m - 1) 2 ≤ p ^ m - 1 := Nat.gcd_le_left 2 (by omega)
      have hpos : 0 < (p ^ m - 1) / Nat.gcd (p ^ m - 1) 2 :=
        Nat.div_pos hg (Nat.gcd_pos_of_pos_right _ (by norm_num))
      have hnle : n ≤ p ^ m + 1 := by
        rw [hord, hcardm] at h
        have := Nat.le_of_dvd hpos h
        have := Nat.div_le_self (p ^ m - 1) (Nat.gcd (p ^ m - 1) 2)
        omega
      exact psl_tail hnle
    · have hm1 : 1 < p ^ m := Nat.one_lt_pow hm hp.one_lt
      have hpos : 0 < (p ^ m + 1) / Nat.gcd (p ^ m - 1) 2 :=
        Nat.div_pos (by have := Nat.gcd_le_right (p ^ m - 1) (by norm_num : 0 < 2); omega)
          (Nat.gcd_pos_of_pos_right _ (by norm_num))
      have hnle : n ≤ p ^ m + 1 := by
        rw [hord, hcardm] at h
        have := Nat.le_of_dvd hpos h
        have := Nat.div_le_self (p ^ m + 1) (Nat.gcd (p ^ m - 1) 2)
        omega
      exact psl_tail hnle
  ·
    exfalso
    have hcardm : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
    rw [Nat.card_congr e.toEquiv, pgl2_card_formula, hcardm] at hdvdH
    have hcm : Nat.Coprime n (p ^ m) := hcop.pow_right m
    have h1 : n ∣ (p ^ m) ^ 2 - 1 := hcm.dvd_of_dvd_mul_left hdvdH
    obtain ⟨k, hk⟩ := hmf
    have h2 : (p ^ m) ^ 2 - 1 ∣ p ^ f - 1 := by
      have := Nat.sub_dvd_pow_sub_pow ((p ^ m) ^ 2) 1 k
      rw [one_pow, ← pow_mul, ← pow_mul] at this
      rw [show m * 2 * k = f by rw [hk]; ring] at this
      rwa [← pow_mul]
    have h3 : n ∣ p ^ f - 1 := h1.trans h2
    have hpf : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
    have h4 : n ∣ 2 := by
      have := Nat.dvd_sub hnq h3
      rwa [show p ^ f + 1 - (p ^ f - 1) = 2 by omega] at this
    exact hn (h4.trans (by norm_num))

theorem map_eq_top_of_cyclic_six {G : Type*} [Group G] {F : Type} [Field F] [Finite F] {p f : ℕ}
    [Fact p.Prime] (hF : Nat.card F = p ^ f) (π : G →* PSL2MatrixGroup F)
    (hkfin : Finite π.ker) (hker : Nat.card π.ker ≤ 2) (hq : 120 ≤ p ^ f) (H : Subgroup G)
    (hns : ¬ Group.IsSolvable (H.map π)) (C : Subgroup G) (hCH : C ≤ H) (hC : IsCyclic C)
    {N : ℕ} (hCcard : Nat.card C = N) (hNq : N ∣ p ^ f + 1) (hNq3 : p ^ f + 1 ≤ 3 * N)
    (h60 : ∀ n, n ∣ 60 → n ∣ p ^ f + 1 → ¬ p ^ f + 1 ≤ 6 * n) : H.map π = ⊤ := by
  have hNpos : 0 < N := by
    have : 0 < p ^ f + 1 := by omega
    exact Nat.pos_of_ne_zero (fun h0 => by rw [h0] at hNq3; omega)
  have hfin : Finite C := Nat.finite_of_card_ne_zero (by rw [hCcard]; omega)
  let φ : C →* PSL2MatrixGroup F := π.comp C.subtype
  have hmul := Subgroup.card_ker_mul_card_range φ
  have hkerφ : Nat.card φ.ker ≤ 2 := by
    refine le_trans ?_ hker
    refine Nat.card_le_card_of_injective
      (fun z : φ.ker => (⟨((z : C) : G), MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp z.2)⟩ : π.ker))
      ?_
    intro a b hab
    have := congrArg (fun z : π.ker => (z : G)) hab
    exact Subtype.ext (Subtype.ext this)
  have hcyc : IsCyclic φ.range := isCyclic_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := φ.range)
  set n := Nat.card φ.range with hn
  have hnpos : 0 < n := Nat.card_pos
  have hN_eq : N = Nat.card φ.ker * n := by rw [← hCcard]; exact hmul.symm
  have hnq : n ∣ p ^ f + 1 := (Dvd.intro_left _ hN_eq.symm).trans hNq
  have hnq2 : p ^ f + 1 ≤ 6 * n := by
    have : N = Nat.card φ.ker * n := hN_eq
    have h1 : Nat.card φ.ker * n ≤ 2 * n := Nat.mul_le_mul_right n hkerφ
    omega
  refine psl2_eq_top_of_orderOf_six hF hq (H.map π) hns (n := n)
    (fun hd => h60 n hd hnq hnq2) hnq hnq2 ⟨(g : PSL2MatrixGroup F), ?_, ?_⟩
  · obtain ⟨c, hc⟩ := g.2
    exact ⟨c, hCH c.2, hc⟩
  · rw [← hg]; exact orderOf_submonoid g

end CFSG.HardMathSupport.Foote.ModuleExclusions
