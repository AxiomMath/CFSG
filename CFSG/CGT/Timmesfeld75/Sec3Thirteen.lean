module

public import CFSG.CGT.Timmesfeld75.Sec3Stmts
public import CFSG.CGT.Timmesfeld75.L2AutStmt
public import CFSG.CGT.Timmesfeld75.Sec3RootGlobal
public import CFSG.CGT.Timmesfeld75.Sec3Six
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.SimpleCase

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups

section QuotConj

variable {G : Type*} [Group G]

theorem exists_quotient_conj_equiv {X N : Subgroup G} [(N.subgroupOf X).Normal] {b : G}
    (hbX : b ∈ Subgroup.normalizer (X : Set G)) (hbN : b ∈ Subgroup.normalizer (N : Set G)) :
    ∃ φ : ↥X ⧸ N.subgroupOf X ≃* ↥X ⧸ N.subgroupOf X, ∀ y : ↥X,
      φ (QuotientGroup.mk y) =
        QuotientGroup.mk (⟨b * y * b⁻¹, (Subgroup.mem_normalizer_iff.1 hbX y).1 y.2⟩ : ↥X) := by
  let ψ : ↥X ≃* ↥X := X.normalizerMonoidHom ⟨b, hbX⟩
  have hψ : ∀ y : ↥X, ((ψ y : ↥X) : G) = b * y * b⁻¹ := fun y => by simp [ψ]
  have hψ' : ∀ y : ↥X, ((ψ.symm y : ↥X) : G) = b⁻¹ * y * b := fun y => by
    have h1 := congrArg Subtype.val (ψ.apply_symm_apply y)
    rw [hψ] at h1
    rw [← h1]
    group
  have he : (N.subgroupOf X).map ψ.toMonoidHom = N.subgroupOf X := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : G) ∈ N := hy
      show ((ψ y : ↥X) : G) ∈ N
      rw [hψ]
      exact (Subgroup.mem_normalizer_iff.1 hbN y).1 hy'
    · intro hz
      have hz' : (z : G) ∈ N := hz
      refine ⟨ψ.symm z, ?_, ψ.apply_symm_apply z⟩
      show ((ψ.symm z : ↥X) : G) ∈ N
      rw [hψ']
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (N : Set G)).inv_mem hbN)
        (z : G)).1 hz'
      simpa using this
  refine ⟨QuotientGroup.congr _ _ ψ he, fun y => ?_⟩
  show QuotientGroup.mk (ψ y) = _
  exact congrArg QuotientGroup.mk (Subtype.ext (hψ y))

theorem quotient_conj_equiv_involutive {X N : Subgroup G} [(N.subgroupOf X).Normal] {b : G}
    (hbX : b ∈ Subgroup.normalizer (X : Set G)) (hbb : b * b = 1)
    (φ : ↥X ⧸ N.subgroupOf X ≃* ↥X ⧸ N.subgroupOf X)
    (hφ : ∀ y : ↥X, φ (QuotientGroup.mk y) =
      QuotientGroup.mk (⟨b * y * b⁻¹, (Subgroup.mem_normalizer_iff.1 hbX y).1 y.2⟩ : ↥X)) :
    ∀ z, φ (φ z) = z := by
  intro z
  refine QuotientGroup.induction_on z fun y => ?_
  rw [hφ y, hφ]
  refine congrArg QuotientGroup.mk (Subtype.ext ?_)
  show b * (b * (y : G) * b⁻¹) * b⁻¹ = y
  calc b * (b * (y : G) * b⁻¹) * b⁻¹ = (b * b) * y * (b * b)⁻¹ := by group
    _ = y := by rw [hbb]; group

theorem map_quotient_conj_equiv {X N K : Subgroup G} [(N.subgroupOf X).Normal] {b : G}
    (hbX : b ∈ Subgroup.normalizer (X : Set G)) (hbK : b ∈ Subgroup.normalizer (K : Set G))
    (hbb : b * b = 1) (φ : ↥X ⧸ N.subgroupOf X ≃* ↥X ⧸ N.subgroupOf X)
    (hφ : ∀ y : ↥X, φ (QuotientGroup.mk y) =
      QuotientGroup.mk (⟨b * y * b⁻¹, (Subgroup.mem_normalizer_iff.1 hbX y).1 y.2⟩ : ↥X)) :
    ((K.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))).map φ.toMonoidHom =
      (K.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X)) := by
  have hle : ((K.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))).map φ.toMonoidHom ≤
      (K.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X)) := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hy' : (y : G) ∈ K := hy
    refine ⟨⟨b * y * b⁻¹, (Subgroup.mem_normalizer_iff.1 hbX y).1 y.2⟩, ?_, (hφ y).symm⟩
    exact (Subgroup.mem_normalizer_iff.1 hbK y).1 hy'
  refine le_antisymm hle fun z hz => ?_
  have hφz : φ z ∈ (K.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X)) :=
    hle (Subgroup.mem_map_of_mem φ.toMonoidHom hz)
  exact ⟨φ z, hφz, quotient_conj_equiv_involutive hbX hbb φ hφ z⟩

end QuotConj

section KeyClaim

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}

set_option quotPrecheck false in
local notation "XQ" => ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)

theorem Sec3.commute_commutator_of_aut [IsSimpleGroup G] (hD : AutInvolDichotomy)
    (h312 : Lemma312Stmt) (hnab : ∃ a b : G, a * b ≠ b * a) (hT : IsWC T) (hglob : Sec3Global T)
    (hiso : Sec3IsoGlobal T) (h16 : Nat.card T ≠ 16) (hS : Sec3 T T₁) (hSiso : Sec3Iso T T₁)
    {x a b : G} (hxT : x ∈ T) (haS : a ∈ T₁) (haT : a ∈ Subgroup.normalizer (T : Set G))
    (hbD : b ∈ classD T) (hbT : b ∈ Subgroup.normalizer (T : Set G))
    (hbS : b ∈ Subgroup.normalizer (T₁ : Set G)) (hab : a * b = b * a) :
    Commute (x * a * x⁻¹ * a⁻¹) b := by
  obtain ⟨hN, f, hf, hpair⟩ := hS.exists_isL2Pair hSiso
  have hbb : b * b = 1 := by
    obtain ⟨k, t, ht, -, hbk⟩ := hbD
    rw [hbk]
    calc k⁻¹ * t * k * (k⁻¹ * t * k) = k⁻¹ * (t * t) * k := by group
      _ = 1 := by rw [elemAbelian_mul_self hT.1 ht]; group
  have hxx : x * x = 1 := elemAbelian_mul_self hT.1 hxT
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hbX : b ∈ Subgroup.normalizer ((T ⊔ T₁ : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_conjSubgroup_eq, conjSubgroup_sup_eq_sup,
      mem_normalizer_iff_conjSubgroup_eq.1 hbT, mem_normalizer_iff_conjSubgroup_eq.1 hbS]
  have hbM : b ∈ Subgroup.normalizer (cfgM T T₁ : Set G) := by
    rw [mem_normalizer_iff_conjSubgroup_eq, ← cfgM_conj, mem_normalizer_iff_conjSubgroup_eq.1 hbT,
      mem_normalizer_iff_conjSubgroup_eq.1 hbS]
  obtain ⟨φ, hφ⟩ := exists_quotient_conj_equiv (X := T ⊔ T₁) (N := cfgM T T₁) hbX hbM
  have hφφ := quotient_conj_equiv_involutive hbX hbb φ hφ
  have hφT := map_quotient_conj_equiv hbX hbT hbb φ hφ
  have hφS := map_quotient_conj_equiv hbX hbS hbb φ hφ
  have hconj : ∃ g : XQ, (T₁.subgroupOf (T ⊔ T₁)).map
      (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) =
      conjSubgroup g ((T.subgroupOf (T ⊔ T₁)).map
        (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) := by
    obtain ⟨y, hy, hy'⟩ := hS.conj
    refine ⟨QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨y, hy⟩, ?_⟩
    rw [← map_conjSubgroup, conjSubgroup_subgroupOf, ← hy']
  rcases hD _ _ _ _ hpair hconj hS.map_ne_map φ hφφ hφT hφS with
    hid | ⟨F, iF, finF, charF, e, σ, hσ, -, -, hσe⟩
  ·
    have hx : x ∈ T ⊔ T₁ := Subgroup.mem_sup_left hxT
    have h1 : x⁻¹ * (b * x * b⁻¹) ∈ cfgM T T₁ := by
      have := hφ ⟨x, hx⟩
      rw [hid] at this
      exact Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 this)
    have hbxb : (x * b * x⁻¹) * b ∈ cfgM T T₁ := by
      have e : x⁻¹ * (b * x * b⁻¹) = (x * b * x⁻¹) * b := by
        rw [hxi, hbi]
        group
      rwa [e] at h1
    have haM : a ∈ cfgM T T₁ := Cfg.normIn_le_cfgM_right T T₁ (mem_normIn.2 ⟨haS, haT⟩)
    have hcomm := elemAbelian_mul_comm hS.cfg.isElemAbelian_cfgM haM hbxb
    have h2 : a * (x * b * x⁻¹) = (x * b * x⁻¹) * a := by
      have h3 : a * (x * b * x⁻¹) * b = (x * b * x⁻¹) * a * b :=
        calc a * (x * b * x⁻¹) * b = a * ((x * b * x⁻¹) * b) := by rw [mul_assoc]
          _ = ((x * b * x⁻¹) * b) * a := hcomm
          _ = (x * b * x⁻¹) * (b * a) := by rw [mul_assoc]
          _ = (x * b * x⁻¹) * (a * b) := by rw [hab]
          _ = (x * b * x⁻¹) * a * b := (mul_assoc _ _ _).symm
      exact mul_right_cancel h3
    have h4 : (x * a * x⁻¹) * b = b * (x * a * x⁻¹) := by
      have h5 := congrArg (fun z => x⁻¹ * z * x) h2
      have e1 : x⁻¹ * (a * (x * b * x⁻¹)) * x = (x⁻¹ * a * x) * b := by group
      have e2 : x⁻¹ * ((x * b * x⁻¹) * a) * x = b * (x⁻¹ * a * x) := by group
      rw [e1, e2, hxi] at h5
      rw [hxi]
      exact h5
    exact Commute.mul_left h4 (Commute.inv_left hab)
  ·
    have hbXc : ∀ y ∈ T ⊔ T₁, b * y * b⁻¹ ∈ T ⊔ T₁ := fun y hy =>
      (Subgroup.mem_normalizer_iff.1 hbX y).1 hy
    have hind : InducesFieldAut (T ⊔ T₁) (cfgM T T₁) b e σ :=
      ⟨hbXc, fun y => by rw [← hφ y]; exact hσe (QuotientGroup.mk y)⟩
    exact absurd (h312 G hnab T T₁ hT hglob hiso hS b hbD hN F iF finF charF e σ hσ hind).1 h16

end KeyClaim

section Family

variable {G : Type} [Group G]

@[expose] def famF {r : ℕ} (Ts : Fin r → Subgroup G) (j : Fin r) : Subgroup G :=
  ⨅ i, normIn (Ts j) (Ts i)

theorem mem_famF {r : ℕ} {Ts : Fin r → Subgroup G} {j : Fin r} {a : G} :
    a ∈ famF Ts j ↔ ∀ i, a ∈ Ts j ∧ a ∈ Subgroup.normalizer (Ts i : Set G) := by
  simp only [famF, Subgroup.mem_iInf, mem_normIn]

theorem famF_le {r : ℕ} (Ts : Fin r → Subgroup G) (j : Fin r) : famF Ts j ≤ Ts j :=
  fun _ ha => (mem_famF.1 ha j).1

structure Cfg313 (T : Subgroup G) {r : ℕ} (Ts : Fin r → Subgroup G) : Prop where
  wc : IsWC T
  inj : Function.Injective Ts
  conj : ∀ i, ∃ g : G, Ts i = conjSubgroup g T
  ne : ∀ j, famF Ts j ≠ ⊥

theorem isElemAbelian_iSup_of_comm {ι : Type*} (K : ι → Subgroup G)
    (hsq : ∀ i, ∀ x ∈ K i, x ^ 2 = 1) (hcomm : ∀ i j, ∀ a ∈ K i, ∀ b ∈ K j, a * b = b * a) :
    IsElemAbelian 2 (⨆ i, K i) := by
  have hcomm' : ∀ x ∈ ⨆ i, K i, ∀ y ∈ ⨆ i, K i, Commute x y := by
    intro x hx
    refine Subgroup.iSup_induction K hx (C := fun x => ∀ y ∈ ⨆ i, K i, Commute x y) ?_ ?_ ?_
    · intro i x hxi y hy
      refine Subgroup.iSup_induction K hy (C := fun y => Commute x y) ?_ ?_ ?_
      · intro j y hyj
        exact hcomm i j x hxi y hyj
      · exact Commute.one_right x
      · intro y z hy hz
        exact Commute.mul_right hy hz
    · intro y _
      exact Commute.one_left y
    · intro x y hx hy z hz
      exact Commute.mul_left (hx z hz) (hy z hz)
  have hsq' : ∀ x ∈ ⨆ i, K i, x ^ 2 = 1 := by
    intro x hx
    have := Subgroup.iSup_induction K hx (C := fun x => x ∈ ⨆ i, K i ∧ x ^ 2 = 1)
      (fun i x hxi => ⟨Subgroup.mem_iSup_of_mem i hxi, hsq i x hxi⟩)
      ⟨(⨆ i, K i).one_mem, by simp⟩
      (fun x y hx hy => ⟨(⨆ i, K i).mul_mem hx.1 hy.1, by
        rw [Commute.mul_pow (hcomm' x hx.1 y hy.1), hx.2, hy.2, mul_one]⟩)
    exact this.2
  refine ⟨⟨⟨fun a b => ?_⟩⟩, hsq'⟩
  apply Subtype.ext
  exact hcomm' a a.2 b b.2

variable {T : Subgroup G} {r : ℕ} {Ts : Fin r → Subgroup G}

theorem Cfg313.isWC (c : Cfg313 T Ts) (i : Fin r) : IsWC (Ts i) := by
  obtain ⟨g, hg⟩ := c.conj i
  rw [hg]
  exact c.wc.conj g

theorem Cfg313.exists_conj (c : Cfg313 T Ts) (i j : Fin r) :
    ∃ g : G, Ts j = conjSubgroup g (Ts i) := by
  obtain ⟨gi, hi⟩ := c.conj i
  obtain ⟨gj, hj⟩ := c.conj j
  refine ⟨gj * gi⁻¹, ?_⟩
  rw [hi, hj, conjSubgroup_conjSubgroup]
  congr 1
  group

theorem Cfg313.inf_eq_bot (c : Cfg313 T Ts) {i j : Fin r} (hij : i ≠ j) : Ts i ⊓ Ts j = ⊥ := by
  obtain ⟨g, hg⟩ := c.exists_conj i j
  have hne : conjSubgroup g (Ts i) ≠ Ts i := fun h => hij (c.inj (hg.trans h)).symm
  have := (c.isWC i).inf_conj_eq_bot hne
  rwa [← hg] at this

theorem Cfg313.famF_comm_of_ne (c : Cfg313 T Ts) {i j : Fin r} (hij : i ≠ j) {a d : G}
    (ha : a ∈ famF Ts j) (hd : d ∈ famF Ts i) : a * d = d * a := by
  have ha' := mem_famF.1 ha
  have hd' := mem_famF.1 hd
  exact mul_comm_of_mem_inf_normalizer (c.inf_eq_bot hij) (ha' i).1 (ha' i).2 (hd' i).1 (hd' j).2

theorem Cfg313.famF_comm (c : Cfg313 T Ts) (i j : Fin r) {a d : G} (ha : a ∈ famF Ts i)
    (hd : d ∈ famF Ts j) : a * d = d * a := by
  by_cases hij : i = j
  · subst hij
    exact elemAbelian_mul_comm (c.isWC i).1 ((mem_famF.1 ha i).1) ((mem_famF.1 hd i).1)
  · exact c.famF_comm_of_ne (Ne.symm hij) ha hd

theorem Cfg313.isElemAbelian_iSup_famF (c : Cfg313 T Ts) : IsElemAbelian 2 (⨆ j, famF Ts j) :=
  isElemAbelian_iSup_of_comm (famF Ts) (fun j x hx => (c.isWC j).1.2 x (famF_le Ts j hx))
    fun i j _ ha _ hb => c.famF_comm i j ha hb

end Family

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {T : Subgroup G} {r : ℕ}
  {Ts : Fin r → Subgroup G}

theorem Cfg313.commutator_mem_famF (hD : AutInvolDichotomy) (h312 : Lemma312Stmt)
    (hnab : ∃ a b : G, a * b ≠ b * a) (c : Cfg313 T Ts) (hglob : Sec3Global T)
    (hiso : Sec3IsoGlobal T) (h16 : Nat.card T ≠ 16) {i j : Fin r} {x a : G} (hx : x ∈ Ts i)
    (ha : a ∈ famF Ts j) : x * a * x⁻¹ * a⁻¹ ∈ famF Ts i := by
  by_cases hij : i = j
  · subst hij
    have hcomm : x * a = a * x := elemAbelian_mul_comm (c.isWC i).1 hx (mem_famF.1 ha i).1
    have : x * a * x⁻¹ * a⁻¹ = 1 := by rw [hcomm]; group
    rw [this]
    exact (famF Ts i).one_mem
  · obtain ⟨gi, hgi⟩ := c.conj i
    have hglob_i : Sec3Global (Ts i) := hgi ▸ hglob.conj gi
    have hiso_i : Sec3IsoGlobal (Ts i) := hgi ▸ hiso.conj gi
    have h16_i : Nat.card (Ts i) ≠ 16 := by rw [hgi, card_conjSubgroup]; exact h16
    obtain ⟨g, hg⟩ := c.exists_conj i j
    have hne : conjSubgroup g (Ts i) ≠ Ts i := fun h => hij (c.inj (hg.trans h)).symm
    have hL : normIn (Ts i) (conjSubgroup g (Ts i)) ≠ ⊥ := by
      rw [← hg]
      intro h
      exact c.ne i (le_bot_iff.1 (h ▸ iInf_le (fun l => normIn (Ts i) (Ts l)) j))
    have hS : Sec3 (Ts i) (Ts j) := by
      have := hglob_i g hne hL
      rwa [← hg] at this
    have hI : Sec3Iso (Ts i) (Ts j) := by
      have := hiso_i g hne hL
      rwa [← hg] at this
    have hwT : x * a * x⁻¹ * a⁻¹ ∈ Ts i := by
      have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
      rw [e]
      exact (Ts i).mul_mem hx
        (conj_mem_of_mem_normalizer (mem_famF.1 ha i).2 ((Ts i).inv_mem hx))
    rw [mem_famF]
    refine fun l => ⟨hwT, ?_⟩
    obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (c.ne l)
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    have hbl := mem_famF.1 hb
    have hbD : b ∈ classD (Ts i) := by
      obtain ⟨g', hg'⟩ := c.exists_conj i l
      have hbm : b ∈ conjSubgroup g' (Ts i) := hg' ▸ (hbl l).1
      have ht : g'⁻¹ * b * g' ∈ Ts i := mem_conjSubgroup.1 hbm
      refine ⟨g'⁻¹, g'⁻¹ * b * g', ht, fun h => hb1' ?_, by group⟩
      calc b = g' * (g'⁻¹ * b * g') * g'⁻¹ := by group
        _ = 1 := by rw [h]; group
    have hcomm := Sec3.commute_commutator_of_aut hD h312 hnab (c.isWC i) hglob_i hiso_i h16_i hS hI
      hx (mem_famF.1 ha j).1 (mem_famF.1 ha i).2 hbD (hbl i).2 (hbl j).2 (c.famF_comm j l ha hb)
    exact (c.isWC l).centralizer_le_normalizer (hbl l).1 hb1'
      (Subgroup.mem_centralizer_singleton_iff.2 hcomm)

theorem Cfg313.conj_famF_eq (hD : AutInvolDichotomy) (h312 : Lemma312Stmt)
    (hnab : ∃ a b : G, a * b ≠ b * a) (c : Cfg313 T Ts) (hglob : Sec3Global T)
    (hiso : Sec3IsoGlobal T) (h16 : Nat.card T ≠ 16) {i : Fin r} {x : G} (hx : x ∈ Ts i) :
    conjSubgroup x (⨆ j, famF Ts j) = ⨆ j, famF Ts j := by
  have hle : ∀ y ∈ Ts i, conjSubgroup y (⨆ j, famF Ts j) ≤ ⨆ j, famF Ts j := by
    intro y hy
    show (⨆ j, famF Ts j).map (MulAut.conj y).toMonoidHom ≤ _
    rw [Subgroup.map_iSup]
    refine iSup_le fun j => ?_
    rintro _ ⟨a, ha, rfl⟩
    have ha' : a ∈ famF Ts j := ha
    have hmem := c.commutator_mem_famF hD h312 hnab hglob hiso h16 hy ha'
    have e : (MulAut.conj y).toMonoidHom a = (y * a * y⁻¹ * a⁻¹) * a := by
      simp [MulAut.conj_apply]
    rw [e]
    exact (⨆ j, famF Ts j).mul_mem (Subgroup.mem_iSup_of_mem i hmem)
      (Subgroup.mem_iSup_of_mem j ha')
  refine le_antisymm (hle x hx) ?_
  have := hle x⁻¹ ((Ts i).inv_mem hx)
  rwa [conjSubgroup_le_iff, inv_inv] at this

theorem Cfg313.conj_iSup_famF (hD : AutInvolDichotomy) (h312 : Lemma312Stmt)
    (hnab : ∃ a b : G, a * b ≠ b * a) (c : Cfg313 T Ts) (hglob : Sec3Global T)
    (hiso : Sec3IsoGlobal T) (h16 : Nat.card T ≠ 16) :
    ∀ x ∈ ⨆ i, Ts i, conjSubgroup x (⨆ j, famF Ts j) = ⨆ j, famF Ts j := by
  have hle : (⨆ i, Ts i) ≤ Subgroup.normalizer ((⨆ j, famF Ts j : Subgroup G) : Set G) :=
    iSup_le fun i x hx =>
      mem_normalizer_of_conjSubgroup_eq (c.conj_famF_eq hD h312 hnab hglob hiso h16 hx)
  exact fun x hx => mem_normalizer_iff_conjSubgroup_eq.1 (hle hx)

end Main

theorem lemma313_of (hD : AutInvolDichotomy) (h312 : Lemma312Stmt) : Lemma313Stmt := by
  intro G _ _ _ hnab T hT hglob hiso h16 r Ts _ hinj hconj hTi hne
  have c : Cfg313 T Ts := ⟨hT, hinj, hconj, hne⟩
  refine ⟨c.isElemAbelian_iSup_famF, c.conj_iSup_famF hD h312 hnab hglob hiso h16, ?_⟩
  obtain ⟨i₀, hi₀⟩ := hTi
  have hTR : T ≤ ⨆ i, Ts i := hi₀ ▸ le_iSup Ts i₀
  have hQR : (⨆ j, famF Ts j) ≤ ⨆ i, Ts i :=
    iSup_le fun j => (famF_le Ts j).trans (le_iSup Ts j)
  have hRQ : (⨆ i, Ts i) ≤ Subgroup.normalizer ((⨆ j, famF Ts j : Subgroup G) : Set G) :=
    fun x hx =>
      mem_normalizer_of_conjSubgroup_eq (c.conj_iSup_famF hD h312 hnab hglob hiso h16 x hx)
  have hQcore : (⨆ j, famF Ts j) ≤ pCoreOf 2 (⨆ i, Ts i) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQR hRQ
      (isPGroup_two_of_isElemAbelian c.isElemAbelian_iSup_famF)
  have hRN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (⨆ i, Ts i)
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (hne i₀)
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hu' : u ∈ famF Ts i₀ := hu
  have huT : u ∈ T := hi₀ ▸ famF_le Ts i₀ hu'
  refine isRootInvolutionSet_classDIn_of_normIn_ne_bot hglob hT hTR fun h hh g hg _ => ?_
  refine Subgroup.ne_bot_iff_exists_ne_one.2
    ⟨⟨h * u * h⁻¹, mem_normIn.2 ⟨?_, ?_⟩⟩, fun h' => hu1' ?_⟩
  · exact mem_conjSubgroup.2 (by simpa [mul_assoc] using huT)
  · exact pCoreOf_le_normalizer_conjSubgroup hT hTR hg
      ((Subgroup.mem_normalizer_iff.1 (hRN hh) u).1 (hQcore (Subgroup.mem_iSup_of_mem i₀ hu')))
  · have h1 : h * u * h⁻¹ = 1 := congrArg Subtype.val h'
    calc u = h⁻¹ * (h * u * h⁻¹) * h := by group
      _ = 1 := by rw [h1]; group

end CFSG.CGT.Timmesfeld75
