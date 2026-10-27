module

public import CFSG.Quasithin.Background.ConjTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.Family

section Conj

variable {W : Type} [CommGroup W]

@[expose] def conjSub (c : MulAut W) (B : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  B.map (MulAut.conj c).toMonoidHom

theorem mem_conjSub {c : MulAut W} {B : Subgroup (MulAut W)} {x : MulAut W} :
    x ∈ conjSub c B ↔ ∃ b ∈ B, c * b * c⁻¹ = x := by
  simp only [conjSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem conj_mem_conjSub {c : MulAut W} {B : Subgroup (MulAut W)} {b : MulAut W} (hb : b ∈ B) :
    c * b * c⁻¹ ∈ conjSub c B :=
  mem_conjSub.2 ⟨b, hb, rfl⟩

theorem fixV_conjSub (c : MulAut W) (B : Subgroup (MulAut W)) :
    fixV (conjSub c B) = (fixV B).map (c : W ≃* W).toMonoidHom :=
  CFSG.Quasithin.fixV_map_conj_eq B c

theorem index_fixV_conjSub (c : MulAut W) (B : Subgroup (MulAut W)) :
    (fixV (conjSub c B)).index = (fixV B).index :=
  CFSG.Quasithin.ConjTransport.index_fixV_map_conj B c

@[expose] def conjSup (B : Subgroup (MulAut W)) : List (MulAut W) → Subgroup (MulAut W)
  | [] => ⊥
  | c :: cs => conjSub c B ⊔ conjSup B cs

theorem conjSub_le_conjSup (B : Subgroup (MulAut W)) {cs : List (MulAut W)} {c : MulAut W}
    (hc : c ∈ cs) : conjSub c B ≤ conjSup B cs := by
  induction cs with
  | nil => simp at hc
  | cons d cs ih =>
    rw [conjSup]
    rcases List.mem_cons.1 hc with rfl | hc
    · exact le_sup_left
    · exact (ih hc).trans le_sup_right

theorem index_fixV_conjSup_le [Finite W] (B : Subgroup (MulAut W)) (cs : List (MulAut W)) :
    (fixV (conjSup B cs)).index ≤ (fixV B).index ^ cs.length := by
  induction cs with
  | nil => simp [conjSup, fixV_bot]
  | cons c cs ih =>
    rw [conjSup, fixV_sup, List.length_cons, pow_succ]
    refine Subgroup.index_inf_le.trans ?_
    rw [index_fixV_conjSub]
    calc (fixV B).index * (fixV (conjSup B cs)).index
        ≤ (fixV B).index * (fixV B).index ^ cs.length := Nat.mul_le_mul le_rfl ih
      _ = (fixV B).index ^ cs.length * (fixV B).index := by ring

end Conj

section Gen

variable {W : Type} [CommGroup W] [Finite W]

theorem exists_list_map_eq {G A : Type*} [Group G] [Group A] (φ : G →* A) :
    ∀ cs : List A, (∀ c ∈ cs, c ∈ φ.range) → ∃ cs' : List G, cs'.map φ = cs := by
  intro cs
  induction cs with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons c cs ih =>
    intro h
    obtain ⟨g, hg⟩ := h c List.mem_cons_self
    obtain ⟨cs', hcs'⟩ := ih fun d hd => h d (List.mem_cons_of_mem c hd)
    exact ⟨g :: cs', by simp [hg, hcs']⟩

@[expose] def liftW {G : Subgroup (MulAut W)} (cs' : List ↥G) : List (MulAut W) :=
  cs'.map (fun c : ↥G => (c : MulAut W))

omit [Finite W] in
theorem length_liftW {G : Subgroup (MulAut W)} (cs' : List ↥G) : (liftW cs').length = cs'.length := by
  simp [liftW]

@[expose] def conjGen {G : Subgroup (MulAut W)} (B : Subgroup (MulAut W)) (cs' : List ↥G) :
    Set ↥G :=
  {y | ∃ c ∈ cs', ∃ b : ↥G, (b : MulAut W) ∈ B ∧ y = c * b * c⁻¹}

omit [Finite W] in
theorem map_closure_conjGen_le {G : Subgroup (MulAut W)} (B : Subgroup (MulAut W))
    (cs' : List ↥G) :
    (Subgroup.closure (conjGen B cs')).map G.subtype ≤ conjSup B (liftW cs') := by
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨y, ⟨c, hc, b, hb, rfl⟩, rfl⟩
  have h1 : ((c * b * c⁻¹ : ↥G) : MulAut W) ∈ conjSub (c : MulAut W) B := by
    have := conj_mem_conjSub (c := (c : MulAut W)) hb
    simpa using this
  exact conjSub_le_conjSup B (List.mem_map.2 ⟨c, hc, rfl⟩) h1

omit [Finite W] in
theorem map_closure_conjGen {G : Subgroup (MulAut W)} {A : Type} [Group A] (φ : ↥G →* A)
    (B : Subgroup (MulAut W)) (cs' : List ↥G) :
    (Subgroup.closure (conjGen B cs')).map φ =
      Subgroup.closure {y : A | ∃ c ∈ cs'.map φ, ∃ b : ↥G, (b : MulAut W) ∈ B ∧
        y = c * φ b * c⁻¹} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, conjGen, Set.mem_ofPred_eq, List.mem_map]
  constructor
  · rintro ⟨_, ⟨c, hc, b, hb, rfl⟩, rfl⟩
    exact ⟨φ c, ⟨c, hc, rfl⟩, b, hb, by simp⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, b, hb, rfl⟩
    exact ⟨c * b * c⁻¹, ⟨c, hc, b, hb, rfl⟩, by simp⟩

theorem two_pow_le_index_pow_of_mem (hW : ∀ w : W, w * w = 1) {G : Subgroup (MulAut W)} {A : Type}
    [Group A] (φ : ↥G →* A) {B : Subgroup (MulAut W)} (cs : List A)
    (hcs : ∀ c ∈ cs, c ∈ φ.range) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {x : A}
    (hx : orderOf x = p)
    (hmem : x ∈ Subgroup.closure {y : A | ∃ c ∈ cs, ∃ b : ↥G, (b : MulAut W) ∈ B ∧
      y = c * φ b * c⁻¹}) :
    2 ^ orderOf (2 : ZMod p) ≤ (fixV B).index ^ cs.length := by
  obtain ⟨cs', rfl⟩ := exists_list_map_eq φ cs hcs
  set J : Subgroup ↥G := Subgroup.closure (conjGen B cs') with hJ
  have hφJ : J.map φ = Subgroup.closure {y : A | ∃ c ∈ cs'.map φ, ∃ b : ↥G, (b : MulAut W) ∈ B ∧
      y = c * φ b * c⁻¹} := map_closure_conjGen φ B cs'
  have hxJ : x ∈ J.map φ := by rw [hφJ]; exact hmem
  obtain ⟨j, hj, hjx⟩ := Subgroup.mem_map.1 hxJ
  have hdvd : p ∣ orderOf j := by
    have := orderOf_map_dvd φ j
    rwa [hjx, hx] at this
  have hord0 : orderOf j ≠ 0 := (orderOf_pos j).ne'
  set j' : ↥G := j ^ (orderOf j / p) with hj'
  have hj'ord : orderOf j' = p := orderOf_pow_orderOf_div hord0 hdvd
  have hj'J : j' ∈ J := J.pow_mem hj _
  have hj'W : orderOf ((j' : ↥G) : MulAut W) = p := by rw [Subgroup.orderOf_coe, hj'ord]
  have hmemSup : ((j' : ↥G) : MulAut W) ∈ conjSup B (liftW cs') :=
    map_closure_conjGen_le B cs' (Subgroup.mem_map.2 ⟨j', hj'J, rfl⟩)
  have hle : Subgroup.zpowers ((j' : ↥G) : MulAut W) ≤ conjSup B (liftW cs') := by
    rw [Subgroup.zpowers_le]; exact hmemSup
  have h1 := two_pow_orderOf_le_index_fixV hW hp2 hj'W
  have h2 : (fixV (Subgroup.zpowers ((j' : ↥G) : MulAut W))).index ≤
      (fixV (conjSup B (liftW cs'))).index :=
    Subgroup.index_antitone (fixV_anti hle)
  have h3 := index_fixV_conjSup_le B (liftW cs')
  rw [length_liftW] at h3
  rw [List.length_map]
  exact h1.trans (h2.trans h3)


theorem card_le_index_pow_of_closure_eq_top {L : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L) (hL : L ≠ ⊥) {S : Type} [Group S]
    (e : CQ L ≃* S) {B : Subgroup (MulAut W)} (cs : List S)
    (hgen : Subgroup.closure {y : S | ∃ c ∈ cs, ∃ b : ↥L, (b : MulAut W) ∈ B ∧
      y = c * e (QuotientGroup.mk b) * c⁻¹} = ⊤) :
    Nat.card W ≤ (fixV B).index ^ cs.length := by
  let π : ↥L →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center ↥L := by
    ext x
    simp [π]
  have hπapp : ∀ b : ↥L, π b = e (QuotientGroup.mk b) := fun b => rfl
  obtain ⟨cs', rfl⟩ := exists_list_map_eq π cs (fun c _ => hπ c)
  set J : Subgroup ↥L := Subgroup.closure (conjGen B cs') with hJ
  have hmap : J.map π = ⊤ := by
    rw [hJ, map_closure_conjGen π B cs']
    simpa only [hπapp] using hgen
  have hsup : J ⊔ Subgroup.center ↥L = ⊤ := by
    rw [← hker, ← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
  have hJtop : J = ⊤ := eq_top_of_sup_center_eq_top hperf hsup
  have hLle : L ≤ conjSup B (liftW cs') := by
    intro g hg
    apply map_closure_conjGen_le B cs'
    rw [← hJ, hJtop]
    exact Subgroup.mem_map.2 ⟨⟨g, hg⟩, Subgroup.mem_top _, rfl⟩
  have hfix : fixV (conjSup B (liftW cs')) = ⊥ :=
    eq_bot_iff.2 (fun v hv => by
      have : v ∈ fixV L := fixV_anti hLle hv
      rw [fixV_eq_bot_of_irr hirr hL] at this
      exact this)
  have h3 := index_fixV_conjSup_le B (liftW cs')
  rw [hfix, Subgroup.index_bot, length_liftW] at h3
  rw [List.length_map]
  exact h3

end Gen

end CFSG.QuasithinUnique.Setup.X1
