module

public import CFSG.Certificates.Kernel.L52Insp443.OrbSound
public import CFSG.Certificates.Kernel.L52Insp443.CentN

public section

set_option maxRecDepth 20000

namespace CFSG.KC.L52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.Literature.GL52 CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native
  CFSG.SectionRank.QTK.Insp443.PermKit.Native

theorem idK_mem_spanK : ∀ bs : List ℕ, idK ∈ spanK bs
  | [] => by
    rw [spanK_nil]
    exact List.mem_singleton_self _
  | b :: bs => by
    rw [spanK_cons]
    exact List.mem_append_left _ (idK_mem_spanK bs)

theorem gD_mem_subK {bs : List ℕ} {b : ℕ} (hb : b ∈ bs) : gD b ∈ subK bs :=
  Subgroup.subset_closure ⟨b, hb, rfl⟩

theorem exists_subK_of_mem_spanK : ∀ {bs : List ℕ}, (∀ b ∈ bs, unitK b = true) →
    ∀ c ∈ spanK bs, ∃ y ∈ subK bs, mcode (y : Mat) = c
  | [], _, c, hc => by
    rw [spanK_nil, List.mem_singleton] at hc
    exact ⟨1, Subgroup.one_mem _, by rw [kG_one, hc]⟩
  | b :: bs, hu, c, hc => by
    have hmono : subK bs ≤ subK (b :: bs) := Subgroup.closure_mono fun x hx => by
      obtain ⟨d, hd, e⟩ := hx
      exact ⟨d, List.mem_cons_of_mem b hd, e⟩
    have ih := exists_subK_of_mem_spanK (bs := bs) fun d hd => hu d (List.mem_cons_of_mem b hd)
    rw [spanK_cons, List.mem_append] at hc
    rcases hc with hc | hc
    · obtain ⟨y, hy, e⟩ := ih c hc
      exact ⟨y, hmono hy, e⟩
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
      obtain ⟨y, hy, e⟩ := ih s hs
      refine ⟨gD b * y, Subgroup.mul_mem _ (gD_mem_subK List.mem_cons_self) (hmono hy), ?_⟩
      rw [kG_mul, mcode_gD (hu b List.mem_cons_self), e]

theorem mem_spanK_of_subK {bs : List ℕ} (hu : ∀ b ∈ bs, unitK b = true)
    (hcl : ∀ b ∈ bs, ∀ s ∈ spanK bs, mmulK b s ∈ spanK bs) (hsq : ∀ b ∈ bs, mmulK b b = idK)
    {y : G} (hy : y ∈ subK bs) : mcode (y : Mat) ∈ spanK bs := by
  induction hy using Subgroup.closure_induction_left with
  | one =>
    rw [kG_one]
    exact idK_mem_spanK bs
  | mul_left x hx y _ ih =>
    obtain ⟨b, hb, rfl⟩ := hx
    rw [kG_mul, mcode_gD (hu b hb)]
    exact hcl b hb _ ih
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨b, hb, rfl⟩ := hx
    have e : (gD b)⁻¹ = gD b := (gD_inv (hu b hb) (hu b hb) (hsq b hb)).symm
    rw [e, kG_mul, mcode_gD (hu b hb)]
    exact hcl b hb _ ih

theorem mem_subK_of_code {bs : List ℕ} (hu : ∀ b ∈ bs, unitK b = true) {y : G}
    (hy : mcode (y : Mat) ∈ spanK bs) : y ∈ subK bs := by
  obtain ⟨z, hz, e⟩ := exists_subK_of_mem_spanK hu _ hy
  rw [← kG_inj e]
  exact hz

theorem conj_mem_of_gens {bs : List ℕ} {H : Subgroup G} {y : G}
    (h : ∀ b ∈ bs, y * gD b * y⁻¹ ∈ H) {x : G} (hx : x ∈ subK bs) : y * x * y⁻¹ ∈ H := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    exact h b hb
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact H.one_mem
  | mul a c _ _ ha hc =>
    have e : y * (a * c) * y⁻¹ = y * a * y⁻¹ * (y * c * y⁻¹) := by group
    rw [e]
    exact H.mul_mem ha hc
  | inv a _ ha =>
    have e : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
    rw [e]
    exact H.inv_mem ha

theorem mem_normalizer_of_conj {bs : List ℕ} (hu : ∀ b ∈ bs, unitK b = true) {g : G}
    (h : ∀ b ∈ bs, mcode ((g * gD b * g⁻¹ : G) : Mat) ∈ spanK bs) :
    g ∈ Subgroup.normalizer (subK bs : Set G) := by
  have hle : (subK bs).map (MulAut.conj g).toMonoidHom ≤ subK bs := by
    rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_of_gens (fun b hb => mem_subK_of_code hu (h b hb)) hx
  have heq : (subK bs).map (MulAut.conj g).toMonoidHom = subK bs :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hle ⟨x, hx, rfl⟩
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, e⟩ := hx
    have e' : y = x := by
      simpa [MulAut.conj_apply] using e
    rw [← e']
    exact hy

theorem mem_normalizer_iff_conj {bs : List ℕ} (hu : ∀ b ∈ bs, unitK b = true)
    (hcl : ∀ b ∈ bs, ∀ s ∈ spanK bs, mmulK b s ∈ spanK bs) (hsq : ∀ b ∈ bs, mmulK b b = idK)
    (g : G) : g ∈ Subgroup.normalizer (subK bs : Set G) ↔
      ∀ b ∈ bs, mcode ((g * gD b * g⁻¹ : G) : Mat) ∈ spanK bs := by
  constructor
  · intro hg b hb
    exact mem_spanK_of_subK hu hcl hsq ((Subgroup.mem_normalizer_iff.mp hg _).mp (gD_mem_subK hb))
  · exact mem_normalizer_of_conj hu

theorem normP_conj {S bs : List ℕ} (hu : ∀ b ∈ bs, unitK b = true) {y : G}
    (h : normP S bs (mcode (y : Mat)) (mcode ((y⁻¹ : G) : Mat)) = true) :
    ∀ b ∈ bs, mcode ((y * gD b * y⁻¹ : G) : Mat) ∈ S := by
  intro b hb
  have hb' := (memK_iff _ _).mp ((allK_iff _ _).mp h b hb)
  rw [← mcode_gD (hu b hb), code3] at hb'
  exact hb'

theorem normalizer_eq_stabK {bs : List ℕ} (hu : ∀ b ∈ bs, unitK b = true)
    (hcl : ∀ b ∈ bs, ∀ s ∈ spanK bs, mmulK b s ∈ spanK bs) (hsq : ∀ b ∈ bs, mmulK b b = idK)
    {L : List Rec} {a b : G} (hs : Subgroup.closure ({a, b} : Set G) = ⊤) (hm : 0 < L.length)
    (horb : orbOK bs L (normP (spanK bs) bs) (mcode (a : Mat)) (mcode ((a⁻¹ : G) : Mat))
      (mcode (b : Mat)) (mcode ((b⁻¹ : G) : Mat)) = true)
    (hU : ∀ r ∈ L, unitK r.2.1 = true ∧ unitK r.2.2.1 = true) :
    Subgroup.normalizer (subK bs : Set G) = stabK (fixK bs) (fixK_lt bs) ∧
      Nat.card G = L.length * Nat.card (stabK (fixK bs) (fixK_lt bs)) := by
  have ho := orb_sound hs hm horb hU (Subgroup.normalizer (subK bs : Set G))
    fun y hy => (mem_normalizer_iff_conj hu hcl hsq y).mpr (normP_conj hu hy)
  exact ⟨le_antisymm (normalizer_le_stabK hu) ho.2, ho.1⟩

theorem all_iff_forall₂ {p : Table → Bool} {Q : ℕ → Prop} {φ : ℕ → Equiv.Perm (Fin 31)}
    (hp : ∀ T b, Rep 31 T (φ b) → (p T = true ↔ Q b)) :
    ∀ {Ts : List Table} {bs : List ℕ}, List.Forall₂ (Rep 31) Ts (bs.map φ) →
      (Ts.all p = true ↔ ∀ b ∈ bs, Q b)
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | T :: Ts, b :: bs, h => by
    rw [List.map_cons, List.forall₂_cons] at h
    rw [List.all_cons, Bool.and_eq_true, hp T b h.1, all_iff_forall₂ hp h.2, List.forall_mem_cons]

theorem conjIn_iff_codes {us cs : List ℕ} {Us Ts : List Table}
    (hUs : List.Forall₂ (Rep 31) Us (us.map fun u => glPerm (gD u)))
    (hTs : List.Forall₂ (Rep 31) Ts (cs.map fun c => glPerm (gD c)))
    (hcu : ∀ c ∈ cs, unitK c = true) {T : Table} {π : Equiv.Perm (Fin 31)} (hR : Rep 31 T π) :
    conjIn 31 Us (spanTabs 31 Ts) T = true ↔
      ∀ u ∈ us, ∃ y : G, mcode (y : Mat) ∈ spanK cs ∧ π * glPerm (gD u) = glPerm y * π := by
  refine all_iff_forall₂ (φ := fun u => glPerm (gD u)) (fun B u hB => ?_) hUs
  rw [List.any_eq_true]
  constructor
  · rintro ⟨V, hV, hc⟩
    obtain ⟨mask, -, rfl⟩ := List.mem_map.mp hV
    obtain ⟨y, hy, hyr⟩ := exists_code_of_maskProd hTs hcu mask
    exact ⟨y, hy, (compEq_iff hR hB hyr).mp hc⟩
  · rintro ⟨y, hy, e⟩
    obtain ⟨x, hx, mask, hmask, hr⟩ := exists_of_mem_spanK (fun g : G => mcode (g : Mat)) kG_one
      kG_mul gD hn31 glPerm (fun c hc => mcode_gD (hcu c hc)) hTs _ hy
    rw [kG_inj hx] at hr
    refine ⟨maskProd 31 Ts mask, List.mem_map.mpr ⟨mask, List.mem_range.mpr hmask, rfl⟩, ?_⟩
    exact (compEq_iff hR hB hr).mpr e

theorem conj_glPerm_iff {bs : List ℕ} (hu : ∀ b ∈ bs, unitK b = true)
    (hcl : ∀ b ∈ bs, ∀ s ∈ spanK bs, mmulK b s ∈ spanK bs) (hsq : ∀ b ∈ bs, mmulK b b = idK)
    (g : G) : (∀ u ∈ bs, ∃ y : G, mcode (y : Mat) ∈ spanK bs ∧
      glPerm g * glPerm (gD u) = glPerm y * glPerm g) ↔
        g ∈ Subgroup.normalizer (subK bs : Set G) := by
  rw [mem_normalizer_iff_conj hu hcl hsq]
  refine forall₂_congr fun u _ => ⟨fun ⟨y, hy, e⟩ => ?_, fun h => ⟨_, h, ?_⟩⟩
  · rw [← map_mul, ← map_mul] at e
    rw [glPerm_injective e, mul_inv_cancel_right]
    exact hy
  · rw [← map_mul, ← map_mul, inv_mul_cancel_right]

theorem normalizer_of_conj_glPerm {bs : List ℕ} (hu : ∀ b ∈ bs, unitK b = true) {g : G}
    (h : ∀ u ∈ bs, ∃ y : G, mcode (y : Mat) ∈ spanK bs ∧
      glPerm g * glPerm (gD u) = glPerm y * glPerm g) :
    g ∈ Subgroup.normalizer (subK bs : Set G) := by
  refine mem_normalizer_of_conj hu fun u hu' => ?_
  obtain ⟨y, hy, e⟩ := h u hu'
  rw [← map_mul, ← map_mul] at e
  rw [glPerm_injective e, mul_inv_cancel_right]
  exact hy

theorem forall₂_zip : ∀ {a b : List ℕ} {A B : List Table},
    List.Forall₂ (Rep 31) A (a.map fun u => glPerm (gD u)) → (∀ c ∈ a, unitK c = true) →
    List.Forall₂ (Rep 31) B (b.map fun u => glPerm (gD u)) → (∀ c ∈ b, unitK c = true) →
      List.Forall₂ (Rep 31) (List.zipWith (compT 31) A B)
        ((List.zipWith mmulK a b).map fun u => glPerm (gD u)) ∧
        ∀ c ∈ List.zipWith mmulK a b, unitK c = true
  | [], _, A, _, hA, _, _, _ => by
    rw [List.map_nil, List.forall₂_nil_right_iff] at hA
    subst hA
    simp
  | _ :: _, _, [], _, hA, _, _, _ => by
    rw [List.map_cons] at hA
    cases hA
  | _ :: _, [], _ :: _, B, _, _, hB, _ => by
    rw [List.map_nil, List.forall₂_nil_right_iff] at hB
    subst hB
    simp
  | _ :: _, _ :: _, _ :: _, [], _, _, hB, _ => by
    rw [List.map_cons] at hB
    cases hB
  | x :: a, y :: b, X :: A, Y :: B, hA, ua, hB, ub => by
    rw [List.map_cons, List.forall₂_cons] at hA hB
    have hx := ua x List.mem_cons_self
    have hy := ub y List.mem_cons_self
    obtain ⟨ih1, ih2⟩ := forall₂_zip hA.2 (fun c hc => ua c (List.mem_cons_of_mem x hc)) hB.2
      (fun c hc => ub c (List.mem_cons_of_mem y hc))
    have e : mmulK x y = mcode ((gD x * gD y : G) : Mat) := by
      rw [kG_mul, mcode_gD hx, mcode_gD hy]
    refine ⟨?_, ?_⟩
    · rw [List.zipWith_cons_cons, List.zipWith_cons_cons, List.map_cons, List.forall₂_cons]
      refine ⟨?_, ih1⟩
      rw [e, gD_mcode, map_mul]
      exact Rep.compT hA.1 hB.1
    · rw [List.zipWith_cons_cons]
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · rw [e]
        exact unitK_mcode _
      · exact ih2 c hc

@[expose] def PermsK (A : ℕ → Subgroup G) (k : ℕ) (y : G) : Prop :=
  ∀ i < k, ∃ j < k, ∀ x ∈ A i, y * x * y⁻¹ ∈ A j

theorem permsK_one (A : ℕ → Subgroup G) (k : ℕ) : PermsK A k 1 := fun i hi =>
  ⟨i, hi, fun x hx => by rwa [one_mul, inv_one, mul_one]⟩

theorem permsK_mul {A : ℕ → Subgroup G} {k : ℕ} {a b : G} (ha : PermsK A k a)
    (hb : PermsK A k b) : PermsK A k (a * b) := fun i hi => by
  obtain ⟨j, hj, hb'⟩ := hb i hi
  obtain ⟨l, hl, ha'⟩ := ha j hj
  refine ⟨l, hl, fun x hx => ?_⟩
  have e : a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
  rw [e]
  exact ha' _ (hb' x hx)

theorem permsK_pow {A : ℕ → Subgroup G} {k : ℕ} {a : G} (ha : PermsK A k a) :
    ∀ n : ℕ, PermsK A k (a ^ n)
  | 0 => by
    rw [pow_zero]
    exact permsK_one A k
  | n + 1 => by
    rw [pow_succ]
    exact permsK_mul (permsK_pow ha n) ha

@[expose] noncomputable def permSub (A : ℕ → Subgroup G) (k : ℕ) : Subgroup G where
  carrier := {y | PermsK A k y}
  mul_mem' ha hb := permsK_mul ha hb
  one_mem' := permsK_one A k
  inv_mem' {a} ha := by
    have hpos := orderOf_pos a
    have e : a⁻¹ = a ^ (orderOf a - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
    change PermsK A k a⁻¹
    rw [e]
    exact permsK_pow ha _

end CFSG.KC.L52I

end
