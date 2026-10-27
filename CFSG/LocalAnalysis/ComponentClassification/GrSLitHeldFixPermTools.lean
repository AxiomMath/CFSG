module

public import CFSG.Sporadic.SmallOddCore.ClassSimple
public import CFSG.Sporadic.SuzOddCore.Restrict
public import CFSG.LieType.Steinberg.CentralExt.SUThree

public section

namespace CFSG.ComponentClassification.GrSLit.HeldFix

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 Subgroup

theorem tabRep_of_rep {n : ℕ} {t : Tab} {g : Equiv.Perm (Fin n)} (h : Rep n t g)
    (hs : t.size = n) : TabRep t g :=
  ⟨hs, h⟩

theorem rep_comp {n : ℕ} {t s : Tab} {g h : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (hs : Rep n s h) : Rep n (comp n t s) (g * h) := fun x => by
  rw [TabRep.comp_getElem!, hs x, ht (h x)]
  rfl

theorem tabRep_comp_of_rep {n : ℕ} {t s : Tab} {g h : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (hs : Rep n s h) : TabRep (comp n t s) (g * h) :=
  ⟨Array.size_ofFn, rep_comp ht hs⟩

theorem size_wordTabS (m : ℕ) (gs : Array Tab) (w : List ℕ) : (wordTabS m gs w).size = m := by
  cases w with
  | nil => simp [wordTabS, idTab]
  | cons j w => simp [wordTabS, comp]

theorem genGroup_preserves {n : ℕ} {L : List ℕ} {gens : Array Tab} {f : ℕ → Equiv.Perm (Fin n)}
    (hgs : ∀ j < gens.size, Rep n gens[j]! (f j))
    (hL : ∀ j < gens.size, ∀ x ∈ L, (gens[j]!)[x]! ∈ L) :
    ∀ g ∈ genGroup n gens f, ∀ x : Fin n, (x : ℕ) ∈ L → (g x : ℕ) ∈ L := by
  intro g hg x hx
  have hF : ({x : Fin n | (x : ℕ) ∈ L} : Set (Fin n)).Finite := Set.toFinite _
  have h := CFSG.Perm.smul_mem_of_finite_of_mem_closure hF (x := x) (g := g) ?_ hg hx
  · exact h
  · rintro _ ⟨j, hj, rfl⟩ y hy
    have := hL j hj y hy
    show ((f j y : Fin n) : ℕ) ∈ L
    rwa [← hgs j hj y]

section Restrict

variable {n m : ℕ} {L : List ℕ} (hL : PointsList n m L) {gens : Array Tab}
  {f : ℕ → Equiv.Perm (Fin n)}
  (hH : ∀ g ∈ genGroup n gens f, ∀ x : Fin n, (x : ℕ) ∈ L → (g x : ℕ) ∈ L)

@[expose] noncomputable def resGen (j : ℕ) : Equiv.Perm (Fin m) :=
  if hj : j < gens.size then hL.restrHom (genGroup n gens f) hH ⟨f j, subset_closure ⟨j, hj, rfl⟩⟩
  else 1

theorem resGen_of_lt {j : ℕ} (hj : j < gens.size) :
    resGen hL hH j = hL.restrHom (genGroup n gens f) hH ⟨f j, subset_closure ⟨j, hj, rfl⟩⟩ := by
  simp only [resGen, hj, ↓reduceDIte]

theorem tabRep_resGen (hgs : ∀ j < gens.size, Rep n gens[j]! (f j)) :
    ∀ j < (gens.map (restrictArr L)).size,
      TabRep (gens.map (restrictArr L))[j]! (resGen hL hH j) := by
  intro j hj
  have hj' : j < gens.size := by simpa using hj
  rw [getElem!_map_eq _ _ hj', resGen_of_lt hL hH hj']
  exact hL.tabRep_restrHom _ hH _ (hgs j hj')

theorem range_restrHom_eq :
    (hL.restrHom (genGroup n gens f) hH).range =
      genGroup m (gens.map (restrictArr L)) (resGen hL hH) := by
  have htop : (⊤ : Subgroup (genGroup n gens f)) = Subgroup.closure
      (((↑) : genGroup n gens f → Equiv.Perm (Fin n)) ⁻¹' {g | ∃ j < gens.size, f j = g}) :=
    (Subgroup.closure_closure_coe_preimage (k := {g | ∃ j < gens.size, f j = g})).symm
  rw [MonoidHom.range_eq_map, htop, MonoidHom.map_closure]
  congr 1
  ext σ
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_ofPred_eq, Array.size_map]
  constructor
  · rintro ⟨g, ⟨j, hj, hjg⟩, rfl⟩
    refine ⟨j, hj, ?_⟩
    rw [resGen_of_lt hL hH hj]
    exact congrArg _ (Subtype.ext hjg)
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, ⟨j, hj, rfl⟩, (resGen_of_lt hL hH hj).symm⟩

theorem enumerates_range_restrHom (hgs : ∀ j < gens.size, Rep n gens[j]! (f j)) {E : Enum}
    (hE : enumOK m (gens.map (restrictArr L)) E = true) :
    Enumerates (hL.restrHom (genGroup n gens f) hH).range E.tabs.toList := by
  rw [range_restrHom_eq]
  exact enumerates_closure (genGroup_hA (tabRep_resGen hL hH hgs))
    (genGroup_hgens (tabRep_resGen hL hH hgs)) hE

end Restrict

theorem injective_of_card_range {G K : Type*} [Group G] [Group K] [Finite G] (f : G →* K)
    (h : Nat.card f.range = Nat.card G) : Function.Injective f := by
  have hk := Subgroup.card_ker_mul_card_range f
  rw [h] at hk
  have hpos : 0 < Nat.card G := Nat.card_pos
  have h1 : Nat.card f.ker = 1 := by
    have : Nat.card f.ker * Nat.card G = 1 * Nat.card G := by rw [hk, one_mul]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Subgroup.card_eq_one.1 h1

section Klein

variable {G : Type*} [Group G]

theorem zpow_mem_pair_of_sq {d : G} (hd : d * d = 1) (k : ℤ) : d ^ k = 1 ∨ d ^ k = d := by
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  induction k using Int.induction_on with
  | zero => left; simp
  | succ i ih =>
    rw [zpow_add_one]
    rcases ih with h | h <;> rw [h]
    · right; simp
    · left; exact hd
  | pred i ih =>
    rw [zpow_sub_one, hdi]
    rcases ih with h | h <;> rw [h]
    · right; simp
    · left; exact hd

theorem mem_zpowers_of_involution {d g : G} (hd : d * d = 1) (hg : g ∈ zpowers d) :
    g = 1 ∨ g = d := by
  obtain ⟨k, rfl⟩ := hg
  exact zpow_mem_pair_of_sq hd k

theorem mem_normalizer_of_commute {H : Subgroup G} {d : G} (h : ∀ g ∈ H, d * g = g * d) :
    d ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [h g hg, mul_assoc, mul_inv_cancel, mul_one]
    exact hg
  · intro hg
    have hc : Commute d⁻¹ (d * g * d⁻¹) := (Commute.inv_left (h _ hg))
    have e : g = d⁻¹ * (d * g * d⁻¹) * d := by group
    rw [e, hc.eq, mul_assoc, inv_mul_cancel, mul_one]
    exact hg

theorem mem_sup_zpowers_cases {H : Subgroup G} {d : G} (hd : d * d = 1)
    (hdH : d ∈ normalizer (H : Set G)) {g : G} (hg : g ∈ H ⊔ zpowers d) :
    g ∈ H ∨ ∃ h ∈ H, g = h * d := by
  have hnorm : zpowers d ≤ normalizer (H : Set G) := by rwa [zpowers_le]
  have hg' : g ∈ ((H ⊔ zpowers d : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hg'
  obtain ⟨h, hh, _, ⟨k, rfl⟩, rfl⟩ := hg'
  rcases zpow_mem_pair_of_sq hd k with hk | hk
  · left
    simp only [hk, mul_one]
    exact hh
  · right
    exact ⟨h, hh, by simp only [hk]⟩

theorem card_sup_zpowers_of_involution [Finite G] {H : Subgroup G} {d : G} (hd : d * d = 1)
    (hdH : d ∉ H) (hcomm : ∀ h ∈ H, d * h = h * d) :
    Nat.card ↥(H ⊔ zpowers d) = 2 * Nat.card H := by
  have hd1 : d ≠ 1 := fun h => hdH (h ▸ H.one_mem)
  have hord : orderOf d = 2 := orderOf_eq_prime (by rw [pow_two]; exact hd) hd1
  rw [CFSG.LieType.Steinberg.card_sup_zpowers (mem_normalizer_of_commute hcomm) ?_, hord,
    mul_comm]
  intro k hk
  rcases zpow_mem_pair_of_sq hd k with h | h
  · exact h
  · rw [h] at hk
    exact absurd hk hdH

theorem closure_comm_of_pairwise {S : Set G} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) :
    ∀ a ∈ closure S, ∀ b ∈ closure S, a * b = b * a := by
  intro a ha b hb
  have h1 : ∀ b ∈ S, a * b = b * a := by
    intro b hb
    induction ha using Subgroup.closure_induction with
    | mem c hc => exact hS c hc b hb
    | one => simp
    | mul c d _ _ hc hd => rw [mul_assoc, hd, ← mul_assoc, hc, mul_assoc]
    | inv c _ hc =>
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hc, mul_assoc, mul_inv_cancel, mul_one]
  induction hb using Subgroup.closure_induction with
  | mem c hc => exact h1 c hc
  | one => simp
  | mul c d _ _ hc hd => rw [← mul_assoc, hc, mul_assoc, hd, mul_assoc]
  | inv c _ hc =>
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]

theorem closure_sq_of_pairwise {S : Set G} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hsq : ∀ a ∈ S, a * a = 1) : ∀ a ∈ closure S, a * a = 1 := by
  have hcomm := closure_comm_of_pairwise hS
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem c hc => exact hsq c hc
  | one => simp
  | mul c d hc hd hc2 hd2 =>
    calc c * d * (c * d) = c * (d * c) * d := by group
      _ = c * (c * d) * d := by rw [hcomm d hd c hc]
      _ = c * c * (d * d) := by group
      _ = 1 := by rw [hc2, hd2, one_mul]
  | inv c _ hc2 => rw [← mul_inv_rev, hc2, inv_one]

theorem klein_closure [Finite G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hyx : y ≠ x) :
    (∀ a ∈ closure ({x, y} : Set G), ∀ b ∈ closure ({x, y} : Set G), a * b = b * a) ∧
      (∀ a ∈ closure ({x, y} : Set G), a * a = 1) ∧
      Nat.card (closure ({x, y} : Set G)) = 4 := by
  have hS : ∀ a ∈ ({x, y} : Set G), ∀ b ∈ ({x, y} : Set G), a * b = b * a := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      first | rfl | assumption | exact hxy.symm
  refine ⟨closure_comm_of_pairwise hS, closure_sq_of_pairwise hS fun a ha => ?_, ?_⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> assumption
  · have hxy' : closure ({x, y} : Set G) = zpowers x ⊔ zpowers y := by
      rw [Set.insert_eq, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]
    have hx2 : Nat.card (zpowers x) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
    have hyx' : y ∉ zpowers x := fun h => by
      rcases mem_zpowers_of_involution hx h with h | h
      · exact hy1 h
      · exact hyx h
    rw [hxy', card_sup_zpowers_of_involution hy hyx' fun g hg => ?_, hx2]
    rcases mem_zpowers_of_involution hx hg with rfl | rfl
    · simp
    · exact hxy.symm

theorem e8_closure [Finite G] {x y z : G} (hx : x * x = 1) (hy : y * y = 1) (hz : z * z = 1)
    (hxy : x * y = y * x) (hxz : x * z = z * x) (hyz : y * z = z * y) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) (hyx : y ≠ x) (hz1 : z ≠ 1) (hzx : z ≠ x) (hzy : z ≠ y) (hzxy : z ≠ x * y) :
    (∀ a ∈ closure ({x, y, z} : Set G), ∀ b ∈ closure ({x, y, z} : Set G), a * b = b * a) ∧
      (∀ a ∈ closure ({x, y, z} : Set G), a * a = 1) ∧
      Nat.card (closure ({x, y, z} : Set G)) = 8 := by
  have hS : ∀ a ∈ ({x, y, z} : Set G), ∀ b ∈ ({x, y, z} : Set G), a * b = b * a := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first | rfl | assumption | exact hxy.symm | exact hxz.symm | exact hyz.symm
  have hcomm := closure_comm_of_pairwise hS
  refine ⟨hcomm, closure_sq_of_pairwise hS fun a ha => ?_, ?_⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl <;> assumption
  ·
    have hxyz : closure ({x, y, z} : Set G) = zpowers x ⊔ zpowers y ⊔ zpowers z := by
      rw [Set.insert_eq, Set.insert_eq, Subgroup.closure_union, Subgroup.closure_union,
        ← sup_assoc, ← zpowers_eq_closure, ← zpowers_eq_closure, ← zpowers_eq_closure]
    have hx2 : Nat.card (zpowers x) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
    have hyx' : y ∉ zpowers x := fun h => by
      rcases mem_zpowers_of_involution hx h with h | h
      · exact hy1 h
      · exact hyx h
    have hyc : ∀ g ∈ zpowers x, y * g = g * y := by
      intro g hg
      rcases mem_zpowers_of_involution hx hg with rfl | rfl
      · simp
      · exact hxy.symm
    have h4 : Nat.card ↥(zpowers x ⊔ zpowers y) = 4 := by
      rw [card_sup_zpowers_of_involution hy hyx' hyc, hx2]
    have hzB : z ∉ zpowers x ⊔ zpowers y := by
      intro h
      rcases mem_sup_zpowers_cases hy (mem_normalizer_of_commute hyc) h with h' | ⟨g, hg, hzg⟩
      · rcases mem_zpowers_of_involution hx h' with h'' | h''
        · exact hz1 h''
        · exact hzx h''
      · rcases mem_zpowers_of_involution hx hg with rfl | rfl
        · exact hzy (by simpa using hzg)
        · exact hzxy hzg
    rw [hxyz, card_sup_zpowers_of_involution hz hzB fun g hg => ?_, h4]
    have hg' : g ∈ closure ({x, y, z} : Set G) := by
      rw [hxyz]
      exact mem_sup_left hg
    exact hcomm z (subset_closure (by simp)) g hg'

end Klein

theorem exists_conj_eq_map_of_card {G : Type*} [Group G] {H S T : Subgroup G} [Finite H]
    {p : ℕ} [Fact p.Prime] (hS : S ≤ H) (hT : T ≤ H)
    (hcS : Nat.card S = p ^ (Nat.card H).factorization p) (hcT : Nat.card T = Nat.card S) :
    ∃ g ∈ H, T = S.map (MulAut.conj g).toMonoidHom := by
  have hcS' : Nat.card (S.subgroupOf H) = p ^ (Nat.card H).factorization p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hS).toEquiv, hcS]
  have hcT' : Nat.card (T.subgroupOf H) = p ^ (Nat.card H).factorization p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hT).toEquiv, hcT, hcS]
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H (Sylow.ofCard _ hcS') (Sylow.ofCard _ hcT')
  refine ⟨h, h.2, ?_⟩
  have e := congrArg (fun P : Sylow p H => ((P : Subgroup H).map H.subtype)) hh
  simp only [Sylow.coe_ofCard] at e
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hT] at e
  rw [← e]
  ext x
  simp only [Sylow.coe_subgroup_smul, Subgroup.mem_map,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(h : G)⁻¹ * y * h, ?_, ?_⟩
    · have : (MulAut.conj h)⁻¹ • y ∈ S.subgroupOf H := hy
      simpa [MulAut.smul_def, Subgroup.mem_subgroupOf] using this
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
      group
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨(MulAut.conj (h : G)) y, by
      exact H.mul_mem (H.mul_mem h.2 (hS hy)) (H.inv_mem h.2)⟩, ?_, rfl⟩
    show (MulAut.conj h)⁻¹ • _ ∈ S.subgroupOf H
    rw [Subgroup.mem_subgroupOf]
    convert hy using 1
    simp only [MulAut.smul_def, MulAut.conj_inv_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv]
    group

theorem card_center_eq_of_enumerates {n : ℕ} {gs : Array Tab} {f : ℕ → Equiv.Perm (Fin n)}
    (hgs : ∀ j < gs.size, TabRep gs[j]! (f j)) {T : List Tab}
    (hH : Enumerates (genGroup n gs f) T) :
    Nat.card (center (genGroup n gs f)) = (T.filter (commAll n gs)).length := by
  rw [← card_inf_centralizer_of_enum hH hgs]
  set H := genGroup n gs f
  refine Nat.card_congr ⟨fun x => ⟨x.1.1, Subgroup.mem_inf.2 ⟨x.1.2, ?_⟩⟩,
    fun y => ⟨⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩, ?_⟩, ?_, ?_⟩
  · rw [mem_centralizer_iff]
    intro g hg
    have := mem_center_iff.1 x.2 ⟨g, hg⟩
    exact congrArg Subtype.val this
  · rw [mem_center_iff]
    intro g
    apply Subtype.ext
    exact ((mem_centralizer_iff.1 (Subgroup.mem_inf.1 y.2).2) g.1 g.2)
  · intro x
    rfl
  · intro y
    rfl

end CFSG.ComponentClassification.GrSLit.HeldFix
