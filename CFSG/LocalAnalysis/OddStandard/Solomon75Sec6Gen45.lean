module

public import CFSG.Perm.ChainLower
public import CFSG.Sporadic.Recognition.McLASInvolutions
public import CFSG.Sporadic.Recognition.LyonsSimsEndgame
public import CFSG.LocalAnalysis.OddStandard.Solomon75Consistency
public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataMain
public import CFSG.Sporadic.Ly.GenSpecBase
public import Certificates.Certificate36500
public import Certificates.Certificate36501

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.Sporadic.LevelChain CFSG.Sporadic.LevelChain.Native CFSG.Sporadic.Fi23
  CFSG.Sporadic.Fi23.Native CFSG.Sporadic.PairGen

namespace Sec6Gen45

section Check

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

theorem eq_of_rep [FaithfulSMul G (Fin n)] {T : Table} {g h : G} (hg : Rep n T g)
    (hh : Rep n T h) : g = h := by
  refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin n) fun i => Fin.ext ?_
  rw [smul_val_eq_idx, smul_val_eq_idx, ← hg i.val i.isLt, ← hh i.val i.isLt]

theorem commute_of_commTab [FaithfulSMul G (Fin n)] {P Q : Table} {g h : G} (hP : Rep n P g)
    (hQ : Rep n Q h) (hc : commTab n P Q = true) : g * h = h * g := by
  have e : compT n P Q = compT n Q P := by simpa [commTab] using hc
  have h1 : Rep n (compT n P Q) (g * h) := Rep.compT hP hQ
  rw [e] at h1
  exact eq_of_rep h1 (Rep.compT hQ hP)

theorem orderOf_eq_two_of_invoOK [FaithfulSMul G (Fin n)] {P : Table} {g : G} (hP : Rep n P g)
    (h : invoOK n P = true) {p : ℕ} (hp : p < n) (hmove : ¬ap P p = p) : orderOf g = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin n) fun i => Fin.ext ?_
    rw [smul_val_eq_idx, smul_val_eq_idx, idx_sq_of_invoOK hP h i.val i.isLt, idx_one]
  · rintro rfl
    exact hmove (by rw [hP p hp, idx_one])

theorem ne_of_ap_ne {P Q : Table} {g h : G} (hP : Rep n P g) (hQ : Rep n Q h) {p : ℕ}
    (hp : p < n) (hne : ¬ap P p = ap Q p) : g ≠ h := by
  rintro rfl
  exact hne (by rw [hP p hp, hQ p hp])

omit [Group G] [MulAction G (Fin n)] in
theorem prod_orbitSizes (T : Array Tree) :
    ∏ l ∈ Finset.Ico 0 T.size, T[l]!.pts.size = (orbitSizes T).prod := by
  unfold orbitSizes
  rw [← Finset.range_eq_Ico, ← Array.length_toList]
  simp only [← Array.getElem!_toList]
  generalize T.toList = l
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.length_cons, Finset.prod_range_succ', List.map_cons, List.prod_cons, ← ih, mul_comm]
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]

theorem pair_of_pairCheck [Finite G] [FaithfulSMul G (Fin n)] (hn : n < 2 ^ 32)
    {gens : ℤ → Table} {gensG : ℤ → G} (hgens : ∀ z, Rep n (gens z) (gensG z)) {D : PairData}
    (h : pairCheck n gens D = true) (hcard : Nat.card G ≤ D.sizes.prod) :
    ∃ a b z w : G, orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ a * b = b * a ∧ a * z = z * a ∧
      b * w = w * b ∧ closure ({z, w} : Set G) = ⊤ := by
  simp only [pairCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
    and_assoc] at h
  obtain ⟨hslp, hLsz, hinv, hiA, hiB, hpa, hpb, hpab, hinvA, hmA, hinvB, hmB, hAB, hcAB, hcAZ,
    hcBW, hm1, hsts, hs1, hsm, hmono, hnest, hfix, hTsz, htree, hsizes⟩ := h
  set L := slpLetters n gens D.words
  set T := levelTrees n L D.starts D.base
  have hinv' : ∀ j < D.words.size, invOK n L[2 * j]! L[2 * j + 1]! = true :=
    fun j hj => (allIn_eq_true.1 hinv) j (Nat.zero_le _) hj
  have hrep : ∀ j < D.words.size, Rep n L[2 * j]! (slpG gensG D.words j) :=
    rep_slpLetters hn hgens hslp hinv'
  have hmono' : ∀ i < D.base.size, D.starts[i]! ≤ D.starts[i + 1]! := fun i hi => by
    simpa using (allIn_eq_true.1 hmono) i (Nat.zero_le _) hi
  have hs2 : D.starts[0]! + 2 ≤ D.words.size := by
    have := starts_mono hmono' 1 D.base.size hm1 le_rfl
    rw [hs1, hsm] at this
    exact this
  have hA := hrep D.iA hiA
  have hB := hrep D.iB hiB
  have hZ := hrep D.starts[0]! (by omega)
  have hW := hrep (D.starts[0]! + 1) (by omega)
  rw [show 2 * (D.starts[0]! + 1) = 2 * D.starts[0]! + 2 by ring] at hW
  refine ⟨slpG gensG D.words D.iA, slpG gensG D.words D.iB, slpG gensG D.words D.starts[0]!,
    slpG gensG D.words (D.starts[0]! + 1), orderOf_eq_two_of_invoOK hA hinvA hpa hmA,
    orderOf_eq_two_of_invoOK hB hinvB hpb hmB, ne_of_ap_ne hA hB hpab hAB,
    commute_of_commTab hA hB hcAB, commute_of_commTab hA hZ hcAZ,
    commute_of_commTab hB hW hcBW, ?_⟩
  have hnest' : ∀ i, 1 ≤ i → i < D.base.size → ∀ j, D.starts[i]! ≤ j → j < D.starts[i + 1]! →
      slpG gensG D.words j ∈ lvlGroup D.starts (slpG gensG D.words) (i - 1) := by
    unfold nestAt at hnest
    intro i hi1 hi2 j hj1 hj2
    have hw : ∀ z ∈ D.words[j]!,
        D.starts[i - 1]! + 3 ≤ z.natAbs ∧ z.natAbs < D.starts[i]! + 3 := by
      intro z hz
      have := (allIn_eq_true.1 ((allIn_eq_true.1 hnest) i hi1 hi2)) j hj1 hj2
      rw [List.all_eq_true] at this
      simpa using this z hz
    rw [slpG_eq]
    unfold wordG
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hz1, hz2⟩ := hw z hz
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    have hm : slpG gensG D.words (z.natAbs - 3) ∈
        lvlGroup D.starts (slpG gensG D.words) (i - 1) := by
      refine gs_mem_lvlGroup _ (by omega) ?_
      rw [show i - 1 + 1 = i by omega]; omega
    split_ifs
    · exact hm
    · exact Subgroup.inv_mem _ hm
  have hfix' : ∀ i, 1 ≤ i → i < D.base.size → ∀ j, D.starts[i]! ≤ j → j < D.starts[i + 1]! →
      ap L[2 * j]! D.base[i - 1]! = D.base[i - 1]! := by
    intro i hi1 hi2 j hj1 hj2
    simpa using (allIn_eq_true.1 ((allIn_eq_true.1 hfix) i hi1 hi2)) j hj1 hj2
  have htree' : ∀ i < D.base.size, treeOK n D.base[i]! T[i]! L (levelLv D.starts i) = true :=
    fun i hi => (allIn_eq_true.1 htree) i (Nat.zero_le _) hi
  have hlow := card_lvlGroup_ge (n := n) (letters := L) (gs := slpG gensG D.words)
    (starts := D.starts) (base := D.base) (trees := T) (fun j hj => hrep j (by omega))
    (fun j hj => hinv' j (by omega)) (by omega) hsts hmono' htree' hfix' hnest' 0
    (Nat.zero_le _)
  have hprod : ∏ l ∈ Finset.Ico 0 D.base.size, T[l]!.pts.size = D.sizes.prod := by
    rw [← hsizes, ← hTsz]
    exact prod_orbitSizes T
  rw [hprod] at hlow
  have htop : lvlGroup D.starts (slpG gensG D.words) 0 = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _) (hcard.trans hlow))
  rw [eq_top_iff, ← htop]
  refine lvlGroup_le _ _ fun j hj1 hj2 => ?_
  have h01 : D.starts[0 + 1]! = D.starts[0]! + 2 := hs1
  rw [h01] at hj2
  obtain rfl | rfl : j = D.starts[0]! ∨ j = D.starts[0]! + 1 := by omega
  · exact subset_closure (Set.mem_insert _ _)
  · exact subset_closure (Set.mem_insert_of_mem _ rfl)

end Check

theorem exists_pair_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {a b z w : Y}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) (hcab : a * b = b * a)
    (hz : a * z = z * a) (hw : b * w = w * b) (hgen : closure ({z, w} : Set Y) = ⊤) :
    ∃ a' b' : X, orderOf a' = 2 ∧ orderOf b' = 2 ∧ a' ≠ b' ∧ a' * b' = b' * a' ∧
      centralizer ({a'} : Set X) ⊔ centralizer ({b'} : Set X) = ⊤ := by
  refine ⟨e.symm a, e.symm b, by rw [MulEquiv.orderOf_eq]; exact ha,
    by rw [MulEquiv.orderOf_eq]; exact hb, fun h => hab (e.symm.injective h),
    by rw [← map_mul, ← map_mul, hcab], ?_⟩
  have hgen' : closure ({e.symm z, e.symm w} : Set X) = ⊤ := by
    have h := congrArg (Subgroup.map e.symm.toMonoidHom) hgen
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ e.symm.surjective] at h
    rw [← h]
    congr 1
    simp [Set.image_insert_eq, Set.image_singleton]
  rw [eq_top_iff, ← hgen', closure_le]
  rintro _ (rfl | rfl)
  · refine mem_sup_left (mem_centralizer_singleton_iff.2 ?_)
    rw [← map_mul, ← map_mul, hz]
  · refine mem_sup_right (mem_centralizer_singleton_iff.2 ?_)
    rw [← map_mul, ← map_mul, hw]

theorem sup_centralizer_eq_top_of_conj {X : Type*} [Group X] {x y a b g : X}
    (hx : g * x * g⁻¹ = a) (hy : g * y * g⁻¹ = b)
    (h : centralizer ({a} : Set X) ⊔ centralizer ({b} : Set X) = ⊤) :
    centralizer ({x} : Set X) ⊔ centralizer ({y} : Set X) = ⊤ := by
  have hmap : ∀ {u v : X}, g * u * g⁻¹ = v →
      (centralizer ({v} : Set X)).map (MulAut.conj g⁻¹).toMonoidHom ≤
        centralizer ({u} : Set X) := by
    intro u v huv
    rintro _ ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hk
    rw [mem_centralizer_singleton_iff]
    have hu : u = g⁻¹ * v * g := by rw [← huv]; group
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
    rw [hu]
    calc g⁻¹ * k * g * (g⁻¹ * v * g) = g⁻¹ * (k * v) * g := by group
      _ = g⁻¹ * (v * k) * g := by rw [hk]
      _ = g⁻¹ * v * g * (g⁻¹ * k * g) := by group
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).surjective, ← h, Subgroup.map_sup]
  exact sup_le_sup (hmap hx) (hmap hy)

theorem eq_one_or_eq_of_mem_center {K : Type*} [Group K] (hc : Nat.card (center K) = 2)
    {c u : K} (hc1 : c ≠ 1) (hcz : c ∈ center K) (hu : u ∈ center K) : u = 1 ∨ u = c := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : center K)).1 hc
  have h1 : (⟨c, hcz⟩ : center K) = y := huniq _ fun h => hc1 (congrArg Subtype.val h)
  have h2 : (⟨u, hu⟩ : center K) = y := huniq _ fun h => hne.1 (congrArg Subtype.val h)
  exact hne.2 (congrArg Subtype.val (h2.trans h1.symm))

theorem exists_conj_pair {X : Type} [Group X] [Finite X] {m : ℕ}
    (hB : AlternatingBalanceData m)
    (hconj : ∀ u v : X, orderOf u = 2 → orderOf v = 2 → IsConj u v)
    (hcov : ∀ t : X, orderOf t = 2 → IsDoubleCoverOfAlt ↥(centralizer ({t} : Set X)) m)
    {x y a b : X} (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x ≠ y) (hc : x * y = y * x)
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) (hc' : a * b = b * a) :
    ∃ g : X, g * x * g⁻¹ = a ∧ g * y * g⁻¹ = b := by
  obtain ⟨c, hcx⟩ := isConj_iff.1 (hconj x a hx ha)
  set y₁ := c * y * c⁻¹ with hy₁def
  have hy₁ : orderOf y₁ = 2 := by
    rw [hy₁def, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hy]
  have hy₁a : y₁ ≠ a := by
    rw [← hcx, hy₁def]
    intro h
    exact hxy (by simpa using h.symm)
  have hy₁c : y₁ * a = a * y₁ := by
    rw [← hcx, hy₁def]
    calc c * y * c⁻¹ * (c * x * c⁻¹) = c * (y * x) * c⁻¹ := by group
      _ = c * (x * y) * c⁻¹ := by rw [hc]
      _ = c * x * c⁻¹ * (c * y * c⁻¹) := by group
  have ha1 : a ≠ 1 := by
    rintro rfl
    simp at ha
  set K := centralizer ({a} : Set X)
  have hK := hcov a ha
  have haK : a ∈ K := mem_centralizer_singleton_iff.2 rfl
  have haZ : (⟨a, haK⟩ : K) ∈ center K := by
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (mem_centralizer_singleton_iff.1 k.2)
  have hnot : ∀ v : X, ∀ hv : v ∈ K, orderOf v = 2 → v ≠ a → (⟨v, hv⟩ : K) ∉ center K := by
    intro v hv hv2 hva hz
    rcases eq_one_or_eq_of_mem_center hK.2.1 (c := ⟨a, haK⟩)
        (fun h => ha1 (congrArg Subtype.val h)) haZ hz with h | h
    · have : v = 1 := congrArg Subtype.val h
      rw [this, orderOf_one] at hv2
      exact absurd hv2 (by norm_num)
    · exact hva (congrArg Subtype.val h)
  have hy₁K : y₁ ∈ K := mem_centralizer_singleton_iff.2 hy₁c
  have hbK : b ∈ K := mem_centralizer_singleton_iff.2 hc'.symm
  obtain ⟨d, hd⟩ := isConj_iff.1 (hB.one_class K hK ⟨y₁, hy₁K⟩ ⟨b, hbK⟩
    (by rw [Subgroup.orderOf_mk]; exact hy₁) (by rw [Subgroup.orderOf_mk]; exact hb)
    (hnot y₁ hy₁K hy₁ hy₁a) (hnot b hbK hb (Ne.symm hab)))
  have hd' : (d : X) * y₁ * (d : X)⁻¹ = b := congrArg Subtype.val hd
  have hda : (d : X) * a = a * d := mem_centralizer_singleton_iff.1 d.2
  refine ⟨d * c, ?_, ?_⟩
  · calc (d : X) * c * x * ((d : X) * c)⁻¹ = d * (c * x * c⁻¹) * (d : X)⁻¹ := by group
      _ = a := by rw [hcx, hda]; group
  · calc (d : X) * c * y * ((d : X) * c)⁻¹ = d * y₁ * (d : X)⁻¹ := by rw [hy₁def]; group
      _ = b := hd'

section McL

open CFSG.Sporadic.Schreier CFSG.Sporadic.McL.Gen45

noncomputable abbrev mclA0 : ↥mclP := ⟨mclGen 0, subset_closure (Set.mem_insert _ _)⟩

noncomputable abbrev mclA1 : ↥mclP := ⟨mclGen 1, subset_closure (Set.mem_insert_of_mem _ rfl)⟩

noncomputable abbrev mclGensG (z : ℤ) : ↥mclP :=
  if z = 1 then mclA0 else if z = -1 then mclA0⁻¹ else if z = 2 then mclA1 else mclA1⁻¹

theorem rep_mclGenTbl {k : ℕ} (hk : k < 13) :
    Rep 275 (mclGenTbl k) (mclGen k) :=
  CFSG.Sporadic.SmallOddCore.rep_arrayMap_ofNat (by norm_num) (rep_mclStrongPerm hk)

theorem rep_subtype {n : ℕ} {t} {S : Subgroup (Equiv.Perm (Fin n))} {g : Equiv.Perm (Fin n)}
    (hg : g ∈ S) (h : Rep n t g) : Rep n t (↑(⟨g, hg⟩ : S)) := h

theorem mcl_pair_gen :
    ∃ a b z w : ↥mclP, orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ a * b = b * a ∧
      a * z = z * a ∧ b * w = w * b ∧ closure ({z, w} : Set ↥mclP) = ⊤ := by
  have h : mclGenCertificate () = true := Certificates.certificate36501
  simp only [mclGenCertificate, mclGenCheck, Bool.and_eq_true] at h
  obtain ⟨⟨hinv0, hinv1⟩, hpair⟩ := h
  have h0 : Rep 275 (mclGenTbl 0) mclA0 := rep_subtype _ (rep_mclGenTbl (by norm_num))
  have h1 : Rep 275 (mclGenTbl 1) mclA1 := rep_subtype _ (rep_mclGenTbl (by norm_num))
  have hgens : ∀ z, Rep 275 (mclLetters (mclGenTbl 0) (mclGenTbl 1) z) (mclGensG z) := by
    intro z
    unfold mclLetters mclGensG
    split_ifs
    · exact h0
    · exact Rep.inv_of_invOK h0 hinv0
    · exact h1
    · exact Rep.inv_of_invOK h1 hinv1
  refine pair_of_pairCheck (by norm_num) hgens hpair ?_
  rw [card_mclP]
  decide

theorem isConj_of_equiv_McL
    {G : Type} [Group G] (e : G ≃* Blueprint.NativeSporadic.McL) (u v : G) (hu : orderOf u = 2)
    (hv : orderOf v = 2) : IsConj u v :=
  @Sporadic.Recognition.LyonsSims.isConj_of_equiv_of_involutions G Blueprint.NativeSporadic.McL _
    Units.instGroup e (fun s t hs ht => Sporadic.Recognition.McLAS.mcl_involutions_conj s t hs ht)
    u v hu hv

end McL

end Sec6Gen45

section McL

open CFSG.Sporadic.Schreier Sec6Gen45

theorem mcl_sup_centralizer_eq_top
    {G : Type} [Group G] [Finite G]
    (e : G ≃* Blueprint.NativeSporadic.McL) {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxy : x ≠ y) (hc : x * y = y * x) :
    centralizer ({x} : Set G) ⊔ centralizer ({y} : Set G) = ⊤ := by
  obtain ⟨a, b, z, w, ha, hb, hab, hcab, hz, hw, hgen⟩ := mcl_pair_gen
  obtain ⟨a', b', ha', hb', hab', hcab', htop⟩ :=
    exists_pair_of_mulEquiv (e.trans mclPermEquiv) ha hb hab hcab hz hw hgen
  have hcov : ∀ t : G, orderOf t = 2 → IsDoubleCoverOfAlt ↥(centralizer ({t} : Set G)) 8 := by
    intro t ht
    obtain ⟨h1, h2, h3⟩ :=
      Sporadic.Recognition.McLCentralizer.mcl_involution_centralizer_alt8_of_certificate ⟨e⟩ ht
    exact isDoubleCoverOfAlt_of_cover ht (by norm_num) h1 h2 h3
  obtain ⟨g, hgx, hgy⟩ := exists_conj_pair alternatingBalanceData_eight_of_certificate
    (isConj_of_equiv_McL e) hcov hx hy hxy hc ha' hb' hab' hcab'
  exact sup_centralizer_eq_top_of_conj hgx hgy htop

end McL

namespace Sec6Gen45

section Ly

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Gen
open CFSG.Sporadic.Ly.Native (matA matB)
open CFSG.Sporadic.He.Native (toMat toMat_apply toMat_mulM toMat_idM toMat_powM mulM powM idM)

theorem mat_pow (g : J) (k : ℕ) : mat (g ^ k) = mat g ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, mat_one]
  | succ k ih => rw [pow_succ, pow_succ, mat_mul, ih]

theorem b_inv_eq : b⁻¹ = b ^ 4 := by
  have h5 : b ^ 5 = 1 := mat_injective (by rw [mat_pow, mat_b, mB_pow, mat_one])
  rw [inv_eq_iff_mul_eq_one, ← pow_succ']
  exact h5

theorem mat_genG (z : ℤ) :
    mat (genG z) = toMat 5 111 (Gen45.letterM matA matB (powM 5 111 matB 4) z) := by
  unfold genG Gen45.letterM
  by_cases h1 : z = 1
  · rw [if_pos h1, if_pos (Or.inl h1), mat_a, toMat_matA]
  · by_cases h2 : z = -1
    · rw [if_neg h1, if_pos h2, if_pos (Or.inr h2), a_inv, mat_a, toMat_matA]
    · rw [if_neg h1, if_neg h2, if_neg (not_or.2 ⟨h1, h2⟩)]
      by_cases h3 : z = 2
      · rw [if_pos h3, if_pos h3, mat_b, toMat_matB]
      · rw [if_neg h3, if_neg h3, b_inv_eq, mat_pow, mat_b, toMat_powM, toMat_matB]

theorem wordM_nil (A B Bi : Array (Array ℕ)) : Gen45.wordM A B Bi [] = idM 111 := by
  simp only [Gen45.wordM, List.foldr_nil]

theorem wordM_cons (A B Bi : Array (Array ℕ)) (z : ℤ) (w : List ℤ) :
    Gen45.wordM A B Bi (z :: w) = mulM 5 111 (Gen45.letterM A B Bi z) (Gen45.wordM A B Bi w) := by
  simp only [Gen45.wordM, List.foldr_cons]

theorem mat_wordG (w : List ℤ) :
    mat (wordG genG w) = toMat 5 111 (Gen45.wordM matA matB (powM 5 111 matB 4) w) := by
  induction w with
  | nil => rw [wordM_nil, toMat_idM, show wordG genG [] = 1 by simp [wordG], mat_one]
  | cons z w ih =>
    rw [show wordG genG (z :: w) = genG z * wordG genG w by simp [wordG], wordM_cons, mat_mul,
      ih, mat_genG, toMat_mulM]

theorem genGs_five (hall : ∀ z ∈ genWords[5]!, z.natAbs ≤ 2) :
    genGs 5 = wordG genG genWords[5]! := by
  unfold genGs
  rw [slpG_eq]
  unfold wordG
  exact congrArg List.prod (List.map_congr_left fun z hz => if_pos (hall z hz))

theorem toMat_ne_of_mod {X Y : Array (Array ℕ)} {i j : ℕ} (hi : i < 111) (hj : j < 111)
    (h : ¬(X[i]!)[j]! % 5 = (Y[i]!)[j]! % 5) : toMat 5 111 X ≠ toMat 5 111 Y := by
  intro e
  have e' := congrFun (congrFun e ⟨i, hi⟩) ⟨j, hj⟩
  rw [toMat_apply, toMat_apply, ZMod.natCast_eq_natCast_iff'] at e'
  exact h e'

theorem toMat_ne_one_of_mod {X : Array (Array ℕ)} {i j : ℕ} (hi : i < 111) (hj : j < 111)
    (hij : i ≠ j) (h : ¬(X[i]!)[j]! % 5 = 0) : toMat 5 111 X ≠ 1 := by
  intro e
  have e' := congrFun (congrFun e ⟨i, hi⟩) ⟨j, hj⟩
  rw [toMat_apply, Matrix.one_apply_ne (fun h' => hij (congrArg Fin.val h')),
    ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero] at e'
  exact h e'

theorem ly_pair_gen :
    ∃ a b z w : ↥J, orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ a * b = b * a ∧
      a * z = z * a ∧ b * w = w * b ∧ Subgroup.closure ({z, w} : Set ↥J) = ⊤ := by
  have h : Gen45.bCertificate () = true := Certificates.certificate36500
  simp only [Gen45.bCertificate, Gen45.bCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    and_assoc] at h
  obtain ⟨hall, hD2, hD02, hD00, hAD, hTD⟩ := h
  have hF := genFacts
  set T := Gen45.wordM matA matB (powM 5 111 matB 4) genWords[5]!
  set D := powM 5 111 (mulM 5 111 matA T) 3 with hD
  have hall' : ∀ z ∈ genWords[5]!, z.natAbs ≤ 2 := by
    intro z hz
    simpa using (List.all_eq_true.1 hall) z hz
  have hmatT : mat (genGs 5) = toMat 5 111 T := by rw [genGs_five hall', mat_wordG]
  have hmatB : mat ((a * genGs 5) ^ 3) = toMat 5 111 D := by
    rw [mat_pow, mat_mul, mat_a, hmatT, hD, toMat_powM, toMat_mulM, toMat_matA]
  have hb2 : (a * genGs 5) ^ 3 * (a * genGs 5) ^ 3 = 1 :=
    mat_injective (by rw [mat_mul, hmatB, ← toMat_mulM, hD2, toMat_idM, mat_one])
  have hb1 : (a * genGs 5) ^ 3 ≠ 1 := by
    intro h1
    refine toMat_ne_one_of_mod (X := D) (i := 0) (j := 2) (by norm_num) (by norm_num)
      (by norm_num) hD02 ?_
    calc toMat 5 111 D = mat ((a * genGs 5) ^ 3) := hmatB.symm
      _ = mat 1 := by rw [h1]
      _ = 1 := mat_one
  refine ⟨a, (a * genGs 5) ^ 3, genGs 4, genGs 5, orderOf_a,
    orderOf_eq_prime (by rw [sq]; exact hb2) hb1, ?_, ?_, gen_a_z hF, ?_, closure_gen_zt hF⟩
  · intro hab
    refine toMat_ne_of_mod (X := D) (Y := matA) (i := 0) (j := 0) (by norm_num) (by norm_num)
      hD00 ?_
    calc toMat 5 111 D = mat ((a * genGs 5) ^ 3) := hmatB.symm
      _ = mat a := by rw [← hab]
      _ = toMat 5 111 matA := by rw [mat_a, toMat_matA]
  · refine mat_injective ?_
    rw [mat_mul, mat_mul, mat_a, hmatB, ← toMat_matA, ← toMat_mulM, ← toMat_mulM, hAD]
  · refine (mat_injective ?_).symm
    rw [mat_mul, mat_mul, hmatT, hmatB, ← toMat_mulM, ← toMat_mulM, hTD]

end Ly

end Sec6Gen45

section Ly

open Sec6Gen45

theorem ly_sup_centralizer_eq_top
    {G : Type} [Group G] [Finite G]
    (e : G ≃* Blueprint.NativeSporadic.Ly) {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxy : x ≠ y) (hc : x * y = y * x) :
    centralizer ({x} : Set G) ⊔ centralizer ({y} : Set G) = ⊤ := by
  obtain ⟨a, b, z, w, ha, hb, hab, hcab, hz, hw, hgen⟩ := ly_pair_gen
  obtain ⟨a', b', ha', hb', hab', hcab', htop⟩ :=
    exists_pair_of_mulEquiv (X := G) (Y := ↥Sporadic.Ly.J) (by exact e.trans Sporadic.Ly.lyEquivJ)
      ha hb hab hcab hz hw hgen
  have hcov : ∀ t : G, orderOf t = 2 → IsDoubleCoverOfAlt ↥(centralizer ({t} : Set G)) 11 :=
    fun t ht => Sporadic.LySchreier.involution_centralizers_quasisimple ⟨e⟩ t ht
  have hconj : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v := fun u v hu hv =>
    @Sporadic.Recognition.LyonsSims.isConj_of_equiv_of_involutions G Blueprint.NativeSporadic.Ly _
      Units.instGroup e
      (fun s t hs ht => Sporadic.Recognition.LyonsSims.ly_isConj_of_involutions hs ht) u v hu hv
  obtain ⟨g, hgx, hgy⟩ := exists_conj_pair alternatingBalanceData_eleven_of_certificate hconj hcov
    hx hy hxy hc ha' hb' hab' hcab'
  exact sup_centralizer_eq_top_of_conj hgx hgy htop

end Ly

end CFSG.OddStandard.Solomon75
