module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Basic

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup

theorem closure_pair_eq_klein {Q : Type} [Group Q] (a b : Q) (ha : a * a = 1) (hb : b * b = 1)
    (hab : Commute a b) :
    closure ({a, b} : Set Q) = GorensteinWalter.kleinFourOfCommutingInvolutions a b ha hb hab := by
  apply le_antisymm
  · rw [closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · change z ∈ ({z * b, z, b, 1} : Set Q)
      simp
    · change z ∈ ({a * z, a, z, 1} : Set Q)
      simp
  · intro z hz
    change z ∈ ({a * b, a, b, 1} : Set Q) at hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact one_mem _

theorem mem_closure_pair_iff {Q : Type} [Group Q] {a b : Q} (ha : a * a = 1) (hb : b * b = 1)
    (hab : Commute a b) (z : Q) :
    z ∈ closure ({a, b} : Set Q) ↔ z = 1 ∨ z = a ∨ z = b ∨ z = a * b := by
  rw [closure_pair_eq_klein a b ha hb hab]
  change z ∈ ({a * b, a, b, 1} : Set Q) ↔ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem isKleinFour_closure_pair {Q : Type} [Group Q] {a b : Q} (ha : a * a = 1) (hb : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) (hab : Commute a b) :
    IsKleinFour ↥(closure ({a, b} : Set Q)) := by
  rw [closure_pair_eq_klein a b ha hb hab]
  exact GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions a b ha hb ha1 hb1 hne hab

theorem commFourAdj_closure_pair {Q : Type} [Group Q] {a b c d : Q}
    (h₁ : IsKleinFour ↥(closure ({a, b} : Set Q))) (h₂ : IsKleinFour ↥(closure ({c, d} : Set Q)))
    (hac : a * c = c * a) (had : a * d = d * a) (hbc : b * c = c * b) (hbd : b * d = d * b) :
    CommFourAdj Q (closure ({a, b} : Set Q)) (closure ({c, d} : Set Q)) := by
  refine ⟨h₁, h₂, ?_⟩
  rw [closure_le, Subgroup.centralizer_closure]
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rw [SetLike.mem_coe, mem_centralizer_iff]
  intro h hh
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
  rcases hz with rfl | rfl <;> rcases hh with rfl | rfl
  · exact hac.symm
  · exact had.symm
  · exact hbc.symm
  · exact hbd.symm

theorem mem_normalizer_closure_pair {Q : Type} [Group Q] [Finite Q] {a b c : Q}
    (ha : c * a * c⁻¹ ∈ closure ({a, b} : Set Q)) (hb : c * b * c⁻¹ ∈ closure ({a, b} : Set Q)) :
    c ∈ normalizer (closure ({a, b} : Set Q) : Set Q) := by
  have hle : (closure ({a, b} : Set Q)).map (MulAut.conj c).toMonoidHom ≤
      closure ({a, b} : Set Q) := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨w, hw, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · simpa using ha
    · simpa using hb
  have hcard : Nat.card (closure ({a, b} : Set Q)) ≤
      Nat.card ((closure ({a, b} : Set Q)).map (MulAut.conj c).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
  have heq : (closure ({a, b} : Set Q)).map (MulAut.conj c).toMonoidHom =
      closure ({a, b} : Set Q) := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    have : c * u * c⁻¹ ∈ (closure ({a, b} : Set Q)).map (MulAut.conj c).toMonoidHom :=
      ⟨u, hu, by simp⟩
    rwa [heq] at this
  · intro hu
    rw [← heq] at hu
    obtain ⟨u', hu', hu'u⟩ := hu
    have : u' = u := (MulAut.conj c).injective (by simpa using hu'u)
    rwa [← this]

theorem exists_mem_ne_ne {Q : Type} [Group Q] [Finite Q] {H : Subgroup Q} (h : 2 < Nat.card H)
    (x y : Q) : ∃ z ∈ H, z ≠ x ∧ z ≠ y := by
  by_contra hc
  have hsub : (H : Set Q) ⊆ {x, y} := fun z hz => by
    by_cases hzx : z = x
    · exact Or.inl hzx
    · by_cases hzy : z = y
      · exact Or.inr hzy
      · exact (hc ⟨z, hz, hzx, hzy⟩).elim
  have hle : Nat.card H ≤ 2 := by
    have e : Nat.card H = (H : Set Q).ncard := Nat.card_coe_set_eq (H : Set Q)
    rw [e]
    calc (H : Set Q).ncard ≤ ({x, y} : Set Q).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({y} : Set Q).ncard + 1 := Set.ncard_insert_le x {y}
      _ = 2 := by rw [Set.ncard_singleton]
  omega

structure FourJoinedData {A : Type} [Group A] (P K : Subgroup A) where
  m : ℕ
  nBig : ℕ
  x : ℕ → A
  y : ℕ → A
  par : ℕ → ℕ
  X : Set A
  nBig_pos : 0 < nBig
  nBig_le : nBig ≤ m
  mem_P : ∀ i < m, x i ∈ P ∧ y i ∈ P
  klein : ∀ i < m, x i ≠ 1 ∧ y i ≠ 1 ∧ x i ≠ y i ∧ x i * x i = 1 ∧ y i * y i = 1 ∧
    x i * y i = y i * x i
  complete : ∀ u v : A, u ∈ K → v ∈ K → u ≠ 1 → v ≠ 1 → u ≠ v → u * u = 1 → v * v = 1 →
    u * v = v * u → ∃ i < m, (u = x i ∨ u = y i ∨ u = x i * y i) ∧
      (v = x i ∨ v = y i ∨ v = x i * y i)
  tree : ∀ i, 0 < i → i < nBig → par i < i ∧ x i * x (par i) = x (par i) * x i ∧
    x i * y (par i) = y (par i) * x i ∧ y i * x (par i) = x (par i) * y i ∧
    y i * y (par i) = y (par i) * y i
  iso : ∀ i, nBig ≤ i → i < m → ∃ g ∈ P, ∃ j < nBig, g * x j * g⁻¹ = x i ∧ g * y j * g⁻¹ = y i
  X_mem : ∀ z ∈ X, z ∈ P
  X_gen : P ≤ closure X
  X_norm : ∀ z ∈ X, ∃ j < nBig,
    (z * x j * z⁻¹ = x j ∨ z * x j * z⁻¹ = y j ∨ z * x j * z⁻¹ = x j * y j) ∧
    (z * y j * z⁻¹ = x j ∨ z * y j * z⁻¹ = y j ∨ z * y j * z⁻¹ = x j * y j)

theorem FourJoinedData.sylowFourJoined {A : Type} [Group A] {P K : Subgroup A} [Finite P]
    (hKP : K ≤ P) (hK : Nat.card K = 2 ^ (Nat.card P).factorization 2)
    (d : FourJoinedData P K) : SylowFourJoined ↥P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨lift, lift_coe⟩ : ∃ lift : A → ↥P, ∀ a ∈ P, ((lift a : ↥P) : A) = a :=
    ⟨fun a => if h : a ∈ P then ⟨a, h⟩ else 1, fun a ha => by simp [ha]⟩
  obtain ⟨xq, xq_coe⟩ : ∃ xq : ℕ → ↥P, ∀ i < d.m, ((xq i : ↥P) : A) = d.x i :=
    ⟨fun i => lift (d.x i), fun i hi => lift_coe _ (d.mem_P i hi).1⟩
  obtain ⟨yq, yq_coe⟩ : ∃ yq : ℕ → ↥P, ∀ i < d.m, ((yq i : ↥P) : A) = d.y i :=
    ⟨fun i => lift (d.y i), fun i hi => lift_coe _ (d.mem_P i hi).2⟩
  obtain ⟨V, hV⟩ : ∃ V : ℕ → Subgroup ↥P, ∀ i, V i = closure ({xq i, yq i} : Set ↥P) :=
    ⟨fun i => closure ({xq i, yq i} : Set ↥P), fun _ => rfl⟩
  have hq : ∀ i < d.m, xq i ≠ 1 ∧ yq i ≠ 1 ∧ xq i ≠ yq i ∧ xq i * xq i = 1 ∧
      yq i * yq i = 1 ∧ xq i * yq i = yq i * xq i := by
    intro i hi
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := d.klein i hi
    have ex := xq_coe i hi
    have ey := yq_coe i hi
    refine ⟨fun h => h1 ?_, fun h => h2 ?_, fun h => h3 ?_, Subtype.ext ?_, Subtype.ext ?_,
      Subtype.ext ?_⟩
    · rw [← ex, h]; rfl
    · rw [← ey, h]; rfl
    · rw [← ex, ← ey, h]
    · show (xq i : A) * (xq i : A) = 1
      rw [ex]; exact h4
    · show (yq i : A) * (yq i : A) = 1
      rw [ey]; exact h5
    · show (xq i : A) * (yq i : A) = (yq i : A) * (xq i : A)
      rw [ex, ey]; exact h6
  have hVk : ∀ i < d.m, IsKleinFour ↥(V i) := fun i hi => by
    rw [hV i]
    exact isKleinFour_closure_pair (hq i hi).2.2.2.1 (hq i hi).2.2.2.2.1 (hq i hi).1
      (hq i hi).2.1 (hq i hi).2.2.1 (hq i hi).2.2.2.2.2
  have hVmem : ∀ i < d.m, ∀ z : ↥P, z ∈ V i ↔ z = 1 ∨ z = xq i ∨ z = yq i ∨ z = xq i * yq i :=
    fun i hi z => by
      rw [hV i]
      exact mem_closure_pair_iff (hq i hi).2.2.2.1 (hq i hi).2.2.2.2.1 (hq i hi).2.2.2.2.2 z
  have hadj : ∀ i, 0 < i → i < d.nBig → CommFourAdj ↥P (V (d.par i)) (V i) := by
    intro i hi0 hi
    obtain ⟨hpar, h1, h2, h3, h4⟩ := d.tree i hi0 hi
    have him : i < d.m := hi.trans_le d.nBig_le
    have hip : d.par i < d.m := hpar.trans him
    have exi := xq_coe i him
    have eyi := yq_coe i him
    have exp := xq_coe _ hip
    have eyp := yq_coe _ hip
    rw [hV, hV]
    refine commFourAdj_closure_pair (by rw [← hV]; exact hVk _ hip) (by rw [← hV]; exact hVk _ him)
      ?_ ?_ ?_ ?_
    · apply Subtype.ext
      show (xq (d.par i) : A) * (xq i : A) = (xq i : A) * (xq (d.par i) : A)
      rw [exi, exp]; exact h1.symm
    · apply Subtype.ext
      show (xq (d.par i) : A) * (yq i : A) = (yq i : A) * (xq (d.par i) : A)
      rw [eyi, exp]; exact h3.symm
    · apply Subtype.ext
      show (yq (d.par i) : A) * (xq i : A) = (xq i : A) * (yq (d.par i) : A)
      rw [exi, eyp]; exact h2.symm
    · apply Subtype.ext
      show (yq (d.par i) : A) * (yq i : A) = (yq i : A) * (yq (d.par i) : A)
      rw [eyi, eyp]; exact h4.symm
  have htree : ∀ i, i < d.nBig → Relation.ReflTransGen (CommFourAdj ↥P) (V 0) (V i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact Relation.ReflTransGen.refl
      · exact (ih _ (d.tree i hi0 hi).1 ((d.tree i hi0 hi).1.trans hi)).tail (hadj i hi0 hi)
  have hX' : closure (lift '' d.X) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    have hsub : P.subtype '' (lift '' d.X) = d.X := by
      ext z
      constructor
      · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
        have := lift_coe w (d.X_mem w hw)
        simp only [Subgroup.coe_subtype, this]
        exact hw
      · intro hz
        exact ⟨lift z, ⟨z, hz, rfl⟩, lift_coe z (d.X_mem z hz)⟩
    have hmap : (closure (lift '' d.X)).map P.subtype = closure d.X := by
      rw [MonoidHom.map_closure, hsub]
    have hq' : (q : A) ∈ (closure (lift '' d.X)).map P.subtype := by
      rw [hmap]
      exact d.X_gen q.2
    obtain ⟨q', hq'1, hq'2⟩ := hq'
    have : q' = q := Subtype.ext hq'2
    rwa [← this]
  have hconj : ∀ g : ↥P, Relation.ReflTransGen (CommFourAdj ↥P) (V 0)
      ((V 0).map (MulAut.conj g).toMonoidHom) := by
    refine reflTransGen_conj_of_closure_eq_top hX' ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨j, hj, hx, hy⟩ := d.X_norm z hz
    have hjm : j < d.m := hj.trans_le d.nBig_le
    have hzP : z ∈ P := d.X_mem z hz
    obtain ⟨c, hc⟩ : ∃ c : ↥P, (c : A) = z := ⟨lift z, lift_coe z hzP⟩
    have hlc : lift z = c := Subtype.ext (by rw [lift_coe z hzP, hc])
    have exj := xq_coe j hjm
    have eyj := yq_coe j hjm
    have key : ∀ (w : ↥P) (a : A), (w : A) = a → ((c * w * c⁻¹ : ↥P) : A) = z * a * z⁻¹ := by
      intro w a hw
      show (c : A) * (w : A) * (c : A)⁻¹ = _
      rw [hc, hw]
    have hprod : ((xq j * yq j : ↥P) : A) = d.x j * d.y j := by
      show (xq j : A) * (yq j : A) = _
      rw [exj, eyj]
    have hcx : c * xq j * c⁻¹ ∈ V j := by
      rw [hVmem j hjm]
      right
      rcases hx with h | h | h
      · left; exact Subtype.ext (by rw [key _ _ exj, h, exj])
      · right; left; exact Subtype.ext (by rw [key _ _ exj, h, eyj])
      · right; right; exact Subtype.ext (by rw [key _ _ exj, h, hprod])
    have hcy : c * yq j * c⁻¹ ∈ V j := by
      rw [hVmem j hjm]
      right
      rcases hy with h | h | h
      · left; exact Subtype.ext (by rw [key _ _ eyj, h, exj])
      · right; left; exact Subtype.ext (by rw [key _ _ eyj, h, eyj])
      · right; right; exact Subtype.ext (by rw [key _ _ eyj, h, hprod])
    refine ⟨V j, htree j hj, ?_⟩
    rw [hlc, hV j]
    rw [hV j] at hcx hcy
    exact mem_normalizer_closure_pair hcx hcy
  have hall : ∀ i < d.m, Relation.ReflTransGen (CommFourAdj ↥P) (V 0) (V i) := by
    intro i hi
    by_cases hib : i < d.nBig
    · exact htree i hib
    · push_neg at hib
      obtain ⟨g, hgP, j, hj, hgx, hgy⟩ := d.iso i hib hi
      have hjm : j < d.m := hj.trans_le d.nBig_le
      obtain ⟨gq, hgq⟩ : ∃ gq : ↥P, (gq : A) = g := ⟨lift g, lift_coe g hgP⟩
      have hx' : (MulAut.conj gq).toMonoidHom (xq j) = xq i := by
        apply Subtype.ext
        show (gq : A) * (xq j : A) * (gq : A)⁻¹ = (xq i : A)
        rw [hgq, xq_coe j hjm, xq_coe i hi, hgx]
      have hy' : (MulAut.conj gq).toMonoidHom (yq j) = yq i := by
        apply Subtype.ext
        show (gq : A) * (yq j : A) * (gq : A)⁻¹ = (yq i : A)
        rw [hgq, yq_coe j hjm, yq_coe i hi, hgy]
      have hVi : V i = (V j).map (MulAut.conj gq).toMonoidHom := by
        rw [hV i, hV j, MonoidHom.map_closure, Set.image_pair, hx', hy']
      rw [hVi]
      exact (hconj gq).trans (reflTransGen_commFourAdj_map_conj (htree j hj) gq)
  have hcardK : Nat.card (K.subgroupOf P) = 2 ^ (Nat.card P).factorization 2 := by
    rw [← hK]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKP).toEquiv
  let S₀ : Sylow 2 ↥P := Sylow.ofCard (K.subgroupOf P) hcardK
  have hS₀ : (S₀ : Subgroup ↥P) = K.subgroupOf P := rfl
  have hfour : ∀ E : Subgroup ↥P, IsKleinFour ↥E → E ≤ (S₀ : Subgroup ↥P) →
      ∃ i < d.m, E = V i := by
    intro E hE hES
    have h4 : Nat.card E = 4 := hE.card_four
    obtain ⟨u, huE, hu1, -⟩ := exists_mem_ne_ne (H := E) (by omega) 1 1
    obtain ⟨v, hvE, hv1, hvu⟩ := exists_mem_ne_ne (H := E) (by omega) 1 u
    have hsq : ∀ w ∈ E, w ^ 2 = 1 := fun w hw => FooteLit.sq_eq_one_of_isKleinFour hE hw
    have huu : u * u = 1 := by rw [← sq]; exact hsq u huE
    have hvv : v * v = 1 := by rw [← sq]; exact hsq v hvE
    have huv : u * v = v * u := FooteLit.commute_of_sq_eq_one hsq huE hvE
    have huK : (u : A) ∈ K := by
      have := hES huE
      rw [hS₀, Subgroup.mem_subgroupOf] at this
      exact this
    have hvK : (v : A) ∈ K := by
      have := hES hvE
      rw [hS₀, Subgroup.mem_subgroupOf] at this
      exact this
    obtain ⟨i, hi, hu3, hv3⟩ := d.complete (u : A) (v : A) huK hvK
      (fun h => hu1 (Subtype.ext h)) (fun h => hv1 (Subtype.ext h))
      (fun h => hvu (Subtype.ext h).symm) (congrArg Subtype.val huu) (congrArg Subtype.val hvv)
      (congrArg Subtype.val huv)
    have hmem : ∀ w : ↥P, ((w : A) = d.x i ∨ (w : A) = d.y i ∨ (w : A) = d.x i * d.y i) →
        w ∈ V i := by
      intro w hw
      rw [hVmem i hi]
      rcases hw with h | h | h
      · right; left; exact Subtype.ext (by rw [xq_coe i hi]; exact h)
      · right; right; left; exact Subtype.ext (by rw [yq_coe i hi]; exact h)
      · right; right; right
        refine Subtype.ext ?_
        show (w : A) = (xq i : A) * (yq i : A)
        rw [xq_coe i hi, yq_coe i hi]; exact h
    have huV : u ∈ V i := hmem u hu3
    have hvV : v ∈ V i := hmem v hv3
    have hEV : E ≤ V i := by
      intro w hw
      rcases FooteLit.mem_of_isKleinFour hE huE hvE hw hu1 hv1 (fun h => hvu h.symm) with
        h | h | h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact huV
      · rw [h]; exact hvV
      · rw [h]; exact mul_mem huV hvV
    exact ⟨i, hi, Subgroup.eq_of_le_of_card_ge hEV (by rw [(hVk i hi).card_four, h4])⟩
  refine sylowFourJoined_of_sylow S₀ fun E F hE hES hF hFS => ?_
  obtain ⟨i, hi, rfl⟩ := hfour E hE hES
  obtain ⟨i', hi', rfl⟩ := hfour F hF hFS
  exact (reflTransGen_commFourAdj_symm (hall i hi)).trans (hall i' hi')

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
