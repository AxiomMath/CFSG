module

public import Certificates.Data.SuzOutComp

public section

namespace CFSG.ComponentClassification.SuzOutComp

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Quasithin Native
open scoped Pointwise

theorem mem_iff_of_isBlock {n : ℕ} {J : Subgroup (Equiv.Perm (Fin n))} {B : Set (Fin n)}
    (hB : MulAction.IsBlock J B) {g : Equiv.Perm (Fin n)} (hg : g ∈ J) {z : Fin n} (hz : z ∈ B)
    (hgz : g z ∈ B) (w : Fin n) : w ∈ B ↔ g w ∈ B := by
  have hgB : (⟨g, hg⟩ : J) • B = B := hB.smul_eq_of_mem (g := (⟨g, hg⟩ : J)) hz hgz
  constructor
  · intro hw
    rw [← hgB]
    exact Set.smul_mem_smul_set hw
  · intro hw
    rw [← hgB] at hw
    exact (Set.smul_mem_smul_set_iff).1 hw

theorem isPreprimitive_of_reach {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] (x : Fin n) (lab : Fin n → ℕ) (root : ℕ → Fin n)
    (hcls : ∀ p : Fin n, ∃ h ∈ J, h x = x ∧ h (root (lab p)) = p)
    (hreach : ∀ y : Fin n, lab y ≠ lab x → ∃ g ∈ J, g x = root (lab y) ∧
      ∀ p : Fin n, ∃ k ∈ Subgroup.closure ({h | h ∈ J ∧ h x = x} ∪ {g}), k x = p) :
    MulAction.IsPreprimitive J (Fin n) := by
  refine MulAction.IsPreprimitive.of_isTrivialBlock_base x fun {B} hxB hB => ?_
  by_cases hsub : ∀ y ∈ B, y = x
  · left
    intro p hp q hq
    rw [hsub p hp, hsub q hq]
  · right
    push Not at hsub
    obtain ⟨y, hyB, hyx⟩ := hsub
    have hroot : ∀ p : Fin n, lab p = lab x → p = x := by
      intro p hp
      obtain ⟨h, -, hhx, hhp⟩ := hcls p
      obtain ⟨h', -, hh'x, hh'r⟩ := hcls x
      have hr : root (lab x) = x := by
        have h1 : h'⁻¹ (h' (root (lab x))) = root (lab x) := by simp
        rw [hh'r] at h1
        rw [← h1, Equiv.Perm.inv_eq_iff_eq, hh'x]
      rw [← hhp, hp, hr, hhx]
    have hlab : lab y ≠ lab x := fun he => hyx (hroot y he)
    obtain ⟨g, hgJ, hgx, hk⟩ := hreach y hlab
    obtain ⟨h, hhJ, hhx, hhy⟩ := hcls y
    have hgxB : g x ∈ B := by
      rw [hgx]
      exact (mem_iff_of_isBlock hB hhJ hxB (by rw [hhx]; exact hxB) _).2 (by rw [hhy]; exact hyB)
    let SB : Subgroup (Equiv.Perm (Fin n)) :=
      { carrier := {k | ∀ w, w ∈ B ↔ k w ∈ B}
        one_mem' := fun w => Iff.rfl
        mul_mem' := fun {a b} ha hb w => (hb w).trans (ha (b w))
        inv_mem' := fun {a} ha w => by simpa using (ha (a⁻¹ w)).symm }
    have hle : Subgroup.closure ({h | h ∈ J ∧ h x = x} ∪ {g}) ≤ SB := by
      rw [Subgroup.closure_le]
      rintro k (⟨hkJ, hkx⟩ | hk')
      · exact mem_iff_of_isBlock hB hkJ hxB (by rw [hkx]; exact hxB)
      · rw [Set.mem_singleton_iff] at hk'
        rw [hk']
        exact mem_iff_of_isBlock hB hgJ hxB hgxB
    refine Set.eq_univ_of_forall fun p => ?_
    obtain ⟨k, hkS, hkp⟩ := hk p
    rw [← hkp]
    exact (hle hkS x).1 hxB

theorem getElem!_push_lt' {S : Array (Array ℕ)} {g : Array ℕ} {h : ℕ} (hh : h < S.size) :
    (S.push g)[h]! = S[h]! := by
  rw [getElem!_pos _ h (by simp; omega), getElem!_pos _ h hh, Array.getElem_push_lt]

theorem getElem!_push_eq' {S : Array (Array ℕ)} {g : Array ℕ} : (S.push g)[S.size]! = g := by
  rw [getElem!_pos _ S.size (by simp), Array.getElem_push_eq]

theorem reachCheck_spec {n k : ℕ} {S : Array (Array ℕ)} {J : Subgroup (Equiv.Perm (Fin n))}
    {x : ℕ} {labels roots : Array ℕ} {tw hw rw : Array (List ℤ)}
    (hSinvA : ∀ j < S.size, isInvA n S[j]! (rawInvs n S)[j]! = true)
    (hSJ : ∀ j < S.size, permOfArr n S[j]! ∈ J)
    (hprim : primCheck n S x labels roots k tw hw = true)
    (h : SuzOutComp.Native.reachCheck n S x labels roots k tw rw = true) (hx : x < n)
    {j : ℕ} (hj : j < k) (hjx : j ≠ labels[x]!) (hr : roots[j]! < n) :
    ∃ g ∈ J, g ⟨x, hx⟩ = ⟨roots[j]!, hr⟩ ∧ ∀ p : Fin n,
      ∃ kk ∈ Subgroup.closure ({h | h ∈ J ∧ h ⟨x, hx⟩ = ⟨x, hx⟩} ∪ {g}), kk ⟨x, hx⟩ = p := by
  have hj' := allLt_spec h hj
  simp only [Bool.or_eq_true, beq_iff_eq, hjx, false_or, Bool.and_eq_true] at hj'
  obtain ⟨hginv, hall⟩ := hj'
  set ga := wordA n S (rawInvs n S) tw[roots[j]!]! with hga
  have hprim' := hprim
  simp only [primCheck, Bool.and_eq_true, decide_eq_true_eq] at hprim'
  obtain ⟨⟨⟨-, -⟩, -⟩, hpall⟩ := hprim'
  have hpr := allLt_spec hpall hr
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hpr
  obtain ⟨⟨⟨⟨⟨⟨htl, htp⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hpr
  obtain ⟨g', hg'J, hg'⟩ := wordA_mem' (K := J) (m := S.size) (fun _ => True)
    (fun j hj => (rep_permOfArr (hSinvA j hj)).1) (fun j hj => (rep_permOfArr (hSinvA j hj)).2)
    (fun j hj _ => hSJ j hj) _ htl (fun _ _ => trivial)
  have hgrep := (rep_permOfArr hginv).1
  have hgg' : permOfArr n ga = g' := hgrep.unique hg'
  set g := permOfArr n ga with hg
  have hgJ : g ∈ J := hgg' ▸ hg'J
  have hgx : g ⟨x, hx⟩ = ⟨roots[j]!, hr⟩ := by
    apply Fin.ext
    rw [← hgrep ⟨x, hx⟩]
    exact htp
  refine ⟨g, hgJ, hgx, fun p => ?_⟩
  have hp := allLt_spec hall p.2
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at hp
  obtain ⟨⟨hpl, hpfix⟩, hpx⟩ := hp
  set K := Subgroup.closure ({h | h ∈ J ∧ h ⟨x, hx⟩ = ⟨x, hx⟩} ∪ {g}) with hK
  have hS' : ∀ i < (S.push ga).size,
      isInvA n (S.push ga)[i]! (rawInvs n (S.push ga))[i]! = true := by
    intro i hi
    rw [rawInvs_getElem! hi]
    rw [Array.size_push] at hi
    rcases Nat.lt_or_ge i S.size with hiS | hiS
    · rw [getElem!_push_lt' hiS, ← rawInvs_getElem! hiS]
      exact hSinvA i hiS
    · have hi' : i = S.size := by omega
      subst hi'
      rw [getElem!_push_eq']
      exact hginv
  obtain ⟨kk, hkK, hkk⟩ := wordA_mem' (K := K) (m := (S.push ga).size)
    (fun i => i = S.size ∨ (i < S.size ∧ (S[i]!)[x]! = x))
    (fun i hi => (rep_permOfArr (hS' i hi)).1) (fun i hi => (rep_permOfArr (hS' i hi)).2)
    (fun i hi hPi => by
      rcases hPi with rfl | ⟨hiS, hix⟩
      · rw [getElem!_push_eq']
        exact Subgroup.subset_closure (Or.inr rfl)
      · rw [getElem!_push_lt' hiS]
        refine Subgroup.subset_closure (Or.inl ⟨hSJ i hiS, Fin.ext ?_⟩)
        rw [← (rep_permOfArr (hSinvA i hiS)).1 ⟨x, hx⟩]
        exact hix)
    _ hpl (fun l hl => by
      have hlt := (List.all_eq_true.1 hpl) l hl
      simp only [bne_iff_ne, ne_eq, Bool.and_eq_true, decide_eq_true_eq] at hlt
      rw [Array.size_push] at hlt
      rcases Nat.lt_or_ge (l.natAbs - 1) S.size with h1 | h1
      · rcases hpfix l hl with hl1 | hl2
        · rw [Array.size_push] at hl1
          omega
        · exact Or.inr ⟨h1, hl2⟩
      · left
        omega)
  refine ⟨kk, hkK, Fin.ext ?_⟩
  rw [← hkk ⟨x, hx⟩]
  exact hpx

theorem isSimpleGroup_of_chain_reach {n k : ℕ} (hn : 2 ≤ n)
    {O S : Array (Array ℕ)} {W : Array (List ℤ)} {base : List (Fin n)} (hbn : base.Nodup)
    {chunks : ℕ} (hc : 0 < chunks) (hO2 : O.size = 2) (hOS : O.size ≤ S.size)
    (hSO : ∀ i < O.size, S[i]! = O[i]!)
    (hchain : rawChainOK n (S.extract 0 O.size) S (base.map Fin.val).toArray W chunks = true)
    {x : ℕ} {labels roots : Array ℕ} {tw hw rw : Array (List ℤ)}
    (hprim : primCheck n S x labels roots k tw hw = true)
    (hreach : SuzOutComp.Native.reachCheck n S x labels roots k tw rw = true)
    {m pa pb pc : ℕ} (hm : (rawOrbitSizes n S (base.map Fin.val).toArray).prod = n * m)
    (ha : orderOf (permOfArr n O[0]!) = pa) (hb : orderOf (permOfArr n O[1]!) = pb)
    (hab : orderOf (permOfArr n O[0]! * permOfArr n O[1]!) = pc)
    (hpq : Nat.Coprime pa pb) (hcm : Nat.Coprime pc m) :
    IsSimpleGroup ↥(Subgroup.closure {g | ∃ k < O.size, permOfArr n O[k]! = g}) := by
  set J := Subgroup.closure {g | ∃ k < O.size, permOfArr n O[k]! = g} with hJ
  have hF := chainCheckFacts hchain
  have hSJ := strong_mem_closure hOS hSO hchain
  obtain ⟨hx, hreach', hroots⟩ := primCheck_spec (J := J) hF.strong_inv hSJ hprim
  have hpt : MulAction.IsPretransitive ↥J (Fin n) := by
    refine ⟨fun p q => ?_⟩
    obtain ⟨g, hg, hgp⟩ := hreach' p
    obtain ⟨g', hg', hgq⟩ := hreach' q
    refine ⟨⟨g' * g⁻¹, J.mul_mem hg' (J.inv_mem hg)⟩, ?_⟩
    show (g' * g⁻¹) p = q
    rw [Equiv.Perm.mul_apply, ← hgp]
    simpa using hgq
  set root : ℕ → Fin n := fun j => if hr : roots[j]! < n then ⟨roots[j]!, hr⟩ else ⟨x, hx⟩
    with hroot
  have hrootval : ∀ (j : ℕ) (hr : roots[j]! < n), root j = ⟨roots[j]!, hr⟩ := fun j hr => by
    rw [hroot]
    exact dite_eq_left hr
  have hprimitive : MulAction.IsPreprimitive ↥J (Fin n) := by
    refine isPreprimitive_of_reach J ⟨x, hx⟩ (fun p => labels[(p : ℕ)]!) root ?_ ?_
    · intro p
      obtain ⟨-, r, hr, g, ⟨hgJ, hgs⟩, hgp⟩ := hroots p
      refine ⟨g, hgJ, ?_, ?_⟩
      · change g ∈ MulAction.stabilizer (Equiv.Perm (Fin n)) (⟨x, hx⟩ : Fin n) at hgs
        rwa [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at hgs
      · have hr' : roots[labels[(p : ℕ)]!]! < n := hr ▸ r.2
        rw [hrootval _ hr']
        have : r = ⟨roots[labels[(p : ℕ)]!]!, hr'⟩ := Fin.ext hr
        rw [← this]
        exact hgp
    · intro y hy
      obtain ⟨hly, r, hr, -⟩ := hroots y
      have hr' : roots[labels[(y : ℕ)]!]! < n := hr ▸ r.2
      obtain ⟨g, hgJ, hgx, hk⟩ :=
        reachCheck_spec hF.strong_inv hSJ hprim hreach hx hly hy hr'
      exact ⟨g, hgJ, by rw [hgx, hrootval _ hr'], hk⟩
  have hO0 : 0 < O.size := by omega
  have hO1 : 1 < O.size := by omega
  let a : ↥J := ⟨permOfArr n O[0]!, Subgroup.subset_closure ⟨0, hO0, rfl⟩⟩
  let b : ↥J := ⟨permOfArr n O[1]!, Subgroup.subset_closure ⟨1, hO1, rfl⟩⟩
  have hgen : Subgroup.closure ({a, b} : Set ↥J) = ⊤ := by
    rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := {g | ∃ k < O.size,
      permOfArr n O[k]! = g})]
    refine Subgroup.closure_mono ?_
    rintro y ⟨k', hk', hy⟩
    rw [hO2] at hk'
    interval_cases k'
    · exact Or.inl (Subtype.ext hy.symm)
    · exact Or.inr (Subtype.ext hy.symm)
  have hJcard : Nat.card ↥J = n * m := by
    have := card_closure_permOfArr_of_rawChainOK (n := n) (by omega) (O := O) (S := S) (W := W)
      hbn hc hOS hSO hchain
    rw [hm] at this
    exact this
  have hstab : Nat.card (MulAction.stabilizer ↥J (⟨x, hx⟩ : Fin n)) = m := by
    have h1 := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥J (⟨x, hx⟩ : Fin n))
    rw [Nat.card_prod, MulAction.orbit_eq_univ, Nat.card_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin, hJcard] at h1
    have hnpos : 0 < n := by omega
    exact Nat.eq_of_mul_eq_mul_left hnpos h1
  have hoa : orderOf a = pa := by rw [← ha]; exact Subgroup.orderOf_mk _ _
  have hob : orderOf b = pb := by rw [← hb]; exact Subgroup.orderOf_mk _ _
  have hoab : orderOf (a * b) = pc := by
    rw [← hab, ← Subgroup.orderOf_coe]
    rfl
  exact CFSG.GroupActions.isSimpleGroup_of_preprimitive_of_coprime_generator_orders
    (by rw [Nat.card_fin]; exact hn) a b hgen (⟨x, hx⟩ : Fin n) (by rw [hoa, hob]; exact hpq)
    (by rw [hoab, hstab]; exact hcm)

end CFSG.ComponentClassification.SuzOutComp
