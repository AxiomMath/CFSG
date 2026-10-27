module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.StepMulti
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SporRec
public import CFSG.HardMathSupport.Dickson.I271.Support.AmbBase

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.Yardstones.Md0ec50421ce4

section Defs

@[expose] def MultiShapeAt (p : ℕ) (Good Rk : ∀ (T : Type) [Group T], Prop) {Q : Type} [Group Q]
    (k : Q) : Prop :=
  PConstrainedShape p (Subgroup.centralizer ({k} : Set Q)) ∨
    ∃ L : List (Subgroup Q), L.length < p ∧
      (∀ J : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) J → J ∈ L) ∧
      ∀ J : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) J →
        Good (PSimple p J) ∧ Rk (PQuot p J)

@[expose] def AtMostOneCompAt (p : ℕ) {Q : Type} [Group Q] (k : Q) : Prop :=
  ∀ I J : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I →
    GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) J → I = J

@[expose] def CentShapeMulti (p : ℕ) (Good Rk : ∀ (T : Type) [Group T], Prop) (Q : Type)
    [Group Q] : Prop :=
  (∀ k : Q, k ≠ 1 → k ^ p = 1 → MultiShapeAt p Good Rk k) ∧
    ∀ E : Subgroup Q, IsElemAbelian p E → ¬ IsCyclic ↥E → ∃ e ∈ E, e ≠ 1 ∧ AtMostOneCompAt p e

end Defs

section Transport

variable {Q Q' : Type} [Group Q] [Finite Q] [Group Q'] [Finite Q']

theorem comp_map_symm {p : ℕ} (hp : p.Prime) (e : Q ≃* Q') (k : Q) {J' : Subgroup Q'}
    (hJ' : GLAPComponent p (Subgroup.centralizer ({e k} : Set Q')) J') :
    GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) (J'.map e.symm.toMonoidHom) := by
  have h1 := glaPComponent_map_equiv hp e.symm hJ'
  have hmap' : (Subgroup.centralizer ({e k} : Set Q')).map e.symm.toMonoidHom =
      Subgroup.centralizer ({k} : Set Q) := by
    rw [map_centralizer_singleton e.symm (e k), MulEquiv.symm_apply_apply]
  rwa [hmap'] at h1

theorem map_map_symm (e : Q ≃* Q') (J' : Subgroup Q') :
    (J'.map e.symm.toMonoidHom).map e.toMonoidHom = J' := by
  rw [Subgroup.map_map]
  have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by ext; simp
  rw [this, Subgroup.map_id]

theorem MultiShapeAt.of_equiv {p : ℕ} (hp : p.Prime) {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (e : Q ≃* Q') {k : Q} (h : MultiShapeAt p Good Rk k) : MultiShapeAt p Good Rk (e k) := by
  have hmap : (Subgroup.centralizer ({k} : Set Q)).map e.toMonoidHom =
      Subgroup.centralizer ({e k} : Set Q') := map_centralizer_singleton e k
  rcases h with hc | ⟨L, hL, hmem, hgood⟩
  · left
    rw [← hmap]
    exact pConstrainedShape_map e hc
  · right
    refine ⟨L.map (Subgroup.map e.toMonoidHom), by simpa using hL, ?_, ?_⟩
    · intro J' hJ'
      have hJ := comp_map_symm hp e k hJ'
      exact List.mem_map.2 ⟨_, hmem _ hJ, map_map_symm e J'⟩
    · intro J' hJ'
      have hJ := comp_map_symm hp e k hJ'
      obtain ⟨hG, hR⟩ := hgood _ hJ
      have hJe := map_map_symm e J'
      refine ⟨?_, ?_⟩
      · have h1 : Good (PSimple p ((J'.map e.symm.toMonoidHom).map e.toMonoidHom)) :=
          hGood _ _ (pSimpleEquiv p (e.subgroupMap (J'.map e.symm.toMonoidHom))) hG
        rwa [hJe] at h1
      · have h1 : Rk (PQuot p ((J'.map e.symm.toMonoidHom).map e.toMonoidHom)) :=
          hRk _ _ (pQuotEquiv p (e.subgroupMap (J'.map e.symm.toMonoidHom))) hR
        rwa [hJe] at h1

theorem AtMostOneCompAt.of_equiv {p : ℕ} (hp : p.Prime) (e : Q ≃* Q') {k : Q}
    (h : AtMostOneCompAt p k) : AtMostOneCompAt p (e k) := by
  intro I' J' hI' hJ'
  have h1 := h _ _ (comp_map_symm hp e k hI') (comp_map_symm hp e k hJ')
  calc I' = (I'.map e.symm.toMonoidHom).map e.toMonoidHom := (map_map_symm e I').symm
    _ = (J'.map e.symm.toMonoidHom).map e.toMonoidHom := by rw [h1]
    _ = J' := map_map_symm e J'

theorem CentShapeMulti.of_equiv {p : ℕ} (hp : p.Prime) {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (e : Q ≃* Q') (h : CentShapeMulti p Good Rk Q) : CentShapeMulti p Good Rk Q' := by
  refine ⟨fun k' hk1 hkp => ?_, fun E' hE' hEnc => ?_⟩
  · set k : Q := e.symm k' with hk
    have hk1' : k ≠ 1 := fun h1 => hk1 (by simpa [hk] using congrArg e h1)
    have hkp' : k ^ p = 1 := by
      apply e.injective
      simpa [hk] using hkp
    have hek : e k = k' := by simp [hk]
    have := MultiShapeAt.of_equiv hp hGood hRk e (h.1 k hk1' hkp')
    rwa [hek] at this
  · have hE : IsElemAbelian p (E'.map e.symm.toMonoidHom) := hE'.map _
    have hEnc' : ¬ IsCyclic ↥(E'.map e.symm.toMonoidHom) := fun hcyc =>
      hEnc ((e.symm.subgroupMap E').isCyclic.2 hcyc)
    obtain ⟨x, hx, hx1, hxo⟩ := h.2 _ hE hEnc'
    refine ⟨e x, ?_, ?_, AtMostOneCompAt.of_equiv hp e hxo⟩
    · obtain ⟨y, hy, rfl⟩ := hx
      simpa using hy
    · intro h1
      apply hx1
      simpa using congrArg e.symm h1

end Transport

section Bridge

variable {X : Type} [Group X] [Finite X]

theorem multi_dichotomy {p : ℕ} (hp : p.Prime) {Good Rk : ∀ (T : Type) [Group T], Prop}
    {K : Subgroup X} (hq : CFSG.Open.IsQuasisimple ↥K) {a k : X} (hk : k ∈ K)
    (hc : k⁻¹ * a ∈ Subgroup.centralizer (K : Set X))
    (h : MultiShapeAt p Good Rk (⟨k, hk⟩ : ↥K)) :
    ∃ L : List (Subgroup X), L.length < p ∧
      (∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J → J ∈ L) ∧
      ∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        Good (PSimple p (J.subgroupOf K)) ∧ Rk (PQuot p (J.subgroupOf K)) := by
  rcases h with hcon | ⟨L, hL, hmem, hgood⟩
  · exact ⟨[], hp.pos, fun J hJ => (not_glaPComponent_of_constrained hp hq hk hc hcon hJ).elim,
      fun J hJ => (not_glaPComponent_of_constrained hp hq hk hc hcon hJ).elim⟩
  · have hsub : ∀ J : Subgroup X,
        GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
          GLAPComponent p (Subgroup.centralizer ({(⟨k, hk⟩ : ↥K)} : Set ↥K)) (J.subgroupOf K) := by
      intro J hJ
      have h1 := glaPComponent_subgroupOf hp
        (inf_le_left : K ⊓ Subgroup.centralizer ({a} : Set X) ≤ K) hJ
      rwa [subgroupOf_inf_centralizer_eq hk hc] at h1
    refine ⟨L.map (Subgroup.map K.subtype), by simpa using hL, ?_, ?_⟩
    · intro J hJ
      have hJK : J ≤ K := hJ.1.trans inf_le_left
      exact List.mem_map.2 ⟨_, hmem _ (hsub J hJ), Subgroup.map_subgroupOf_eq_of_le hJK⟩
    · intro J hJ
      exact hgood _ (hsub J hJ)

theorem atMostOne_of_atMostOneCompAt {p : ℕ} (hp : p.Prime) {K : Subgroup X} {a k : X}
    (hk : k ∈ K) (hc : k⁻¹ * a ∈ Subgroup.centralizer (K : Set X))
    (h : AtMostOneCompAt p (⟨k, hk⟩ : ↥K)) (I J : Subgroup X)
    (hI : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) I)
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) : I = J := by
  have hsub : ∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
      GLAPComponent p (Subgroup.centralizer ({(⟨k, hk⟩ : ↥K)} : Set ↥K)) (J.subgroupOf K) := by
    intro J hJ
    have h1 := glaPComponent_subgroupOf hp
      (inf_le_left : K ⊓ Subgroup.centralizer ({a} : Set X) ≤ K) hJ
    rwa [subgroupOf_inf_centralizer_eq hk hc] at h1
  have hIK : I ≤ K := hI.1.trans inf_le_left
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  have h2 := h _ _ (hsub I hI) (hsub J hJ)
  rw [← Subgroup.map_subgroupOf_eq_of_le hIK, ← Subgroup.map_subgroupOf_eq_of_le hJK, h2]

end Bridge

section Plane

variable {X : Type} [Group X]

@[expose] def InnRel (K : Subgroup X) (x : ↥K) (a : X) : Prop :=
  (x : X)⁻¹ * a ∈ Subgroup.centralizer (K : Set X)

theorem InnRel.one (K : Subgroup X) : InnRel K 1 1 := by
  simpa [InnRel] using (Subgroup.centralizer (K : Set X)).one_mem

theorem InnRel.mul {K : Subgroup X} {x y : ↥K} {a b : X} (hc : InnRel K x a) (hd : InnRel K y b) :
    InnRel K (x * y) (a * b) := by
  have hcy : Commute (y : X)⁻¹ ((x : X)⁻¹ * a) :=
    Commute.inv_left (show Commute (y : X) ((x : X)⁻¹ * a) from
      Subgroup.mem_centralizer_iff.1 hc y y.2)
  have hcy' : (y : X)⁻¹ * ((x : X)⁻¹ * a) = ((x : X)⁻¹ * a) * (y : X)⁻¹ := hcy.eq
  have : (((x * y : ↥K)) : X)⁻¹ * (a * b) = ((x : X)⁻¹ * a) * ((y : X)⁻¹ * b) := by
    calc (((x * y : ↥K)) : X)⁻¹ * (a * b) = ((y : X)⁻¹ * ((x : X)⁻¹ * a)) * b := by
          simp [mul_assoc]
      _ = (((x : X)⁻¹ * a) * (y : X)⁻¹) * b := by rw [hcy']
      _ = ((x : X)⁻¹ * a) * ((y : X)⁻¹ * b) := by simp [mul_assoc]
  unfold InnRel
  rw [this]
  exact Subgroup.mul_mem _ hc hd

theorem InnRel.inv {K : Subgroup X} {x : ↥K} {a : X} (hc : InnRel K x a) : InnRel K x⁻¹ a⁻¹ := by
  have hx : (x : X) * ((x : X)⁻¹ * a)⁻¹ = ((x : X)⁻¹ * a)⁻¹ * (x : X) :=
    Subgroup.mem_centralizer_iff.1 (Subgroup.inv_mem _ hc) x x.2
  have : (((x⁻¹ : ↥K)) : X)⁻¹ * a⁻¹ = ((x : X)⁻¹ * a)⁻¹ := by
    calc (((x⁻¹ : ↥K)) : X)⁻¹ * a⁻¹ = (x : X) * a⁻¹ := by simp
      _ = (x : X) * (a⁻¹ * x) * (x : X)⁻¹ := by simp [mul_assoc]
      _ = (x : X) * ((x : X)⁻¹ * a)⁻¹ * (x : X)⁻¹ := by simp [mul_assoc]
      _ = ((x : X)⁻¹ * a)⁻¹ * (x : X) * (x : X)⁻¹ := by rw [hx]
      _ = ((x : X)⁻¹ * a)⁻¹ := by simp
  unfold InnRel
  rw [this]
  exact Subgroup.inv_mem _ hc

theorem InnRel.pow {K : Subgroup X} {x : ↥K} {a : X} (hc : InnRel K x a) (n : ℕ) :
    InnRel K (x ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using InnRel.one K
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul hc

def imgInner (K A : Subgroup X) : Subgroup ↥K where
  carrier := {x | ∃ a ∈ A, InnRel K x a}
  one_mem' := ⟨1, A.one_mem, InnRel.one K⟩
  mul_mem' := by
    rintro x y ⟨a, ha, hc⟩ ⟨b, hb, hd⟩
    exact ⟨a * b, A.mul_mem ha hb, hc.mul hd⟩
  inv_mem' := by
    rintro x ⟨a, ha, hc⟩
    exact ⟨a⁻¹, A.inv_mem ha, hc.inv⟩

end Plane

section PlaneStep

variable {X : Type} [Group X] [Finite X]

theorem imgInner_comm {K A : Subgroup X} (hZ : Subgroup.center ↥K = ⊥)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {x y : ↥K} (hx : x ∈ imgInner K A)
    (hy : y ∈ imgInner K A) : x * y = y * x := by
  obtain ⟨a, ha, hc⟩ := hx
  obtain ⟨b, hb, hd⟩ := hy
  set c : X := (x : X)⁻¹ * a with hcdef
  set d : X := (y : X)⁻¹ * b with hddef
  have hac : a = (x : X) * c := by rw [hcdef]; group
  have hbd : b = (y : X) * d := by rw [hddef]; group
  have hyc : (y : X) * c = c * (y : X) := Subgroup.mem_centralizer_iff.1 hc y y.2
  have hxd : (x : X) * d = d * (x : X) := Subgroup.mem_centralizer_iff.1 hd x x.2
  have hab := hAcomm a ha b hb
  have e1 : (x : X) * y * (c * d) = (y : X) * x * (d * c) := by
    calc (x : X) * y * (c * d) = (x : X) * (y * c) * d := by group
      _ = (x : X) * (c * y) * d := by rw [hyc]
      _ = ((x : X) * c) * ((y : X) * d) := by group
      _ = a * b := by rw [← hac, ← hbd]
      _ = b * a := hab
      _ = ((y : X) * d) * ((x : X) * c) := by rw [← hac, ← hbd]
      _ = (y : X) * (d * x) * c := by group
      _ = (y : X) * (x * d) * c := by rw [← hxd]
      _ = (y : X) * x * (d * c) := by group
  have e2 : (((y * x)⁻¹ * (x * y) : ↥K) : X) = (d * c) * (c * d)⁻¹ := by
    calc (((y * x)⁻¹ * (x * y) : ↥K) : X) = ((y : X) * x)⁻¹ * ((x : X) * y) := by simp
      _ = ((y : X) * x)⁻¹ * ((x : X) * y * (c * d)) * (c * d)⁻¹ := by group
      _ = ((y : X) * x)⁻¹ * ((y : X) * x * (d * c)) * (c * d)⁻¹ := by rw [e1]
      _ = (d * c) * (c * d)⁻¹ := by group
  have hzC : (((y * x)⁻¹ * (x * y) : ↥K) : X) ∈ Subgroup.centralizer (K : Set X) := by
    rw [e2]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hd hc)
      (Subgroup.inv_mem _ (Subgroup.mul_mem _ hc hd))
  have h1 := Amb.eq_one_of_mem_centralizer hZ (((y * x)⁻¹ * (x * y) : ↥K)).2 hzC
  have h2 : (y * x)⁻¹ * (x * y) = 1 := Subtype.ext h1
  exact (inv_mul_eq_one.1 h2).symm

theorem imgInner_pow {p : ℕ} {K A : Subgroup X} (hZ : Subgroup.center ↥K = ⊥)
    (hAp : ∀ a ∈ A, a ^ p = 1) {x : ↥K} (hx : x ∈ imgInner K A) : x ^ p = 1 := by
  obtain ⟨a, ha, hc⟩ := hx
  set c : X := (x : X)⁻¹ * a with hcdef
  have hac : a = (x : X) * c := by rw [hcdef]; group
  have hxc : Commute (x : X) c := Subgroup.mem_centralizer_iff.1 hc x x.2
  have h1 : (x : X) ^ p * c ^ p = 1 := by
    rw [← hxc.mul_pow, ← hac]
    exact hAp a ha
  have h2 : (x : X) ^ p = (c ^ p)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : (((x ^ p : ↥K)) : X) ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.coe_pow, h2]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc p)
  exact Subtype.ext (Amb.eq_one_of_mem_centralizer hZ (x ^ p : ↥K).2 h3)

theorem isElemAbelian_imgInner {p : ℕ} {K A : Subgroup X} (hZ : Subgroup.center ↥K = ⊥)
    (hAel : IsElemAbelian p A) : IsElemAbelian p (imgInner K A) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · exact imgInner_comm hZ (fun a ha b hb => hAel.comm ha hb) x.2 y.2
  · exact imgInner_pow hZ hAel.2 hx

theorem exists_atMostOne_of_plane {p : ℕ} (hp : p.Prime) {K B A : Subgroup X}
    (hZ : Subgroup.center ↥K = ⊥) (hBel : IsElemAbelian p B)
    (hPlane : ∀ E : Subgroup ↥K, IsElemAbelian p E → ¬ IsCyclic ↥E →
      ∃ e ∈ E, e ≠ 1 ∧ AtMostOneCompAt p e)
    (hAB : A ≤ B) (hAnc : ¬ IsCyclic ↥A) (hAf : A ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (hin : ∀ a ∈ A, ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (K : Set X)) :
    ∃ a ∈ A, a ≠ 1 ∧ ∀ I J : Subgroup X,
      GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) I →
      GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J → I = J := by
  have hAel : IsElemAbelian p A := hBel.mono hAB
  have hEel : IsElemAbelian p (imgInner K A) := isElemAbelian_imgInner hZ hAel
  have hEnc : ¬ IsCyclic ↥(imgInner K A) := by
    intro hcyc
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    obtain ⟨a₀, ha₀, hrel₀⟩ := g.2
    apply hAnc
    refine isCyclic_iff_exists_zpowers_eq_top.2 ⟨⟨a₀, ha₀⟩, ?_⟩
    rw [eq_top_iff]
    rintro ⟨a, ha⟩ -
    obtain ⟨k, hk, hkc⟩ := hin a ha
    let x : ↥(imgInner K A) := ⟨⟨k, hk⟩, ⟨a, ha, hkc⟩⟩
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers).2 (hg x)
    have hxn : (⟨k, hk⟩ : ↥K) = (g : ↥K) ^ n := by
      have := congrArg Subtype.val hn
      simpa [x] using this.symm
    have h1 : InnRel K ((g : ↥K) ^ n) (a₀ ^ n) := hrel₀.pow n
    have h2 : InnRel K ((g : ↥K) ^ n) a := by
      rw [← hxn]
      exact hkc
    have h3 : (a₀ ^ n)⁻¹ * a ∈ Subgroup.centralizer (K : Set X) := by
      set gn : X := (((g : ↥K) ^ n : ↥K) : X) with hgn
      have h1' : gn⁻¹ * a₀ ^ n ∈ Subgroup.centralizer (K : Set X) := h1
      have h2' : gn⁻¹ * a ∈ Subgroup.centralizer (K : Set X) := h2
      have h5 := Subgroup.mul_mem _ (Subgroup.inv_mem _ h1') h2'
      have e : (gn⁻¹ * a₀ ^ n)⁻¹ * (gn⁻¹ * a) = (a₀ ^ n)⁻¹ * a := by group
      rwa [e] at h5
    have h4 : (a₀ ^ n)⁻¹ * a ∈ A ⊓ Subgroup.centralizer (K : Set X) :=
      ⟨A.mul_mem (A.inv_mem (A.pow_mem ha₀ n)) ha, h3⟩
    rw [hAf, Subgroup.mem_bot] at h4
    have h5 : a = a₀ ^ n := by
      have := congrArg (fun t => a₀ ^ n * t) h4
      simpa using this
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    apply Subtype.ext
    simp [h5]
  obtain ⟨e, he, he1, hAtMost⟩ := hPlane _ hEel hEnc
  obtain ⟨a, ha, hrel⟩ := he
  refine ⟨a, ha, ?_, ?_⟩
  · rintro rfl
    apply he1
    have hC : (e : X) ∈ Subgroup.centralizer (K : Set X) := by
      have : (e : X)⁻¹ ∈ Subgroup.centralizer (K : Set X) := by simpa [InnRel] using hrel
      simpa using Subgroup.inv_mem _ this
    exact Subtype.ext (Amb.eq_one_of_mem_centralizer hZ e.2 hC)
  · exact atMostOne_of_atMostOneCompAt hp e.2 hrel hAtMost

end PlaneStep

section Template

variable {X : Type} [Group X] [Finite X]

theorem strong_of_centShapeMulti {name : TauCeti.SporadicName} {p : ℕ}
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) (hP : SporadicOnePairHolds name p)
    (hIH : ∀ (Y : Type) [Group Y] [Finite Y] (J B' : Subgroup Y), CompHyp p J B' →
      Good (↥J ⧸ Subgroup.center ↥J) → Rk ↥J → IsStronglyBalancedIn p B' J)
    (hD : CentShapeMulti p Good Rk (NativeSporadic.Carrier name))
    {K B : Subgroup X} (hC : CompHyp p K B) (hN : I271Norm p K B) (hS : I271SporType K name)
    (hZ : Subgroup.center ↥K = ⊥) : IsStronglyBalancedIn p B K := by
  have hq : CFSG.Open.IsQuasisimple ↥K := hC.quasi
  obtain ⟨e⟩ := hS
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hloc : IsLocallyOneBalancedAbs p (↥K ⧸ Subgroup.center ↥K) :=
    isLocallyOneBalancedAbs_of_pair hOut hBr hC.prime hC.odd hP _ hq.2
      (exists_noncomm_of_isQuasisimple hq) ⟨e⟩
  let eK : ↥K ≃* NativeSporadic.Carrier name :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
      (e.trans (hBr name).some.symm)
  haveI : Finite (NativeSporadic.Carrier name) := Finite.of_equiv ↥K eK.toEquiv
  have hshape : CentShapeMulti p Good Rk ↥K :=
    CentShapeMulti.of_equiv hC.prime hGood hRk eK.symm hD
  refine strong_of_dichotomy_multi hGood hRk hOut hC hN ⟨e⟩ hloc hIH ?_ ?_
  · intro a k hk haB hc haC
    obtain ⟨hkZ, hkp⟩ := lift_data_of_inner (hC.elem.2 a haB) haC hk hc
    have hk1 : (⟨k, hk⟩ : ↥K) ≠ 1 := fun h => hkZ (h ▸ Subgroup.one_mem _)
    have hkp1 : (⟨k, hk⟩ : ↥K) ^ p = 1 := by
      rw [hZ] at hkp
      exact Subgroup.mem_bot.1 hkp
    exact multi_dichotomy hC.prime hq hk hc (hshape.1 _ hk1 hkp1)
  · intro A hAB hAnc hAf hin
    exact exists_atMostOne_of_plane hC.prime hZ hC.elem hshape.2 hAB hAnc hAf hin

theorem sporStrong_of_centShapeMulti {name : TauCeti.SporadicName} {p : ℕ}
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds name p) (hm : ¬ p ∣ sporadicMultiplierOrder name)
    (hIH : ∀ (Y : Type) [Group Y] [Finite Y] (J B' : Subgroup Y), CompHyp p J B' →
      Good (↥J ⧸ Subgroup.center ↥J) → Rk ↥J → IsStronglyBalancedIn p B' J)
    (hD : CentShapeMulti p Good Rk (NativeSporadic.Carrier name)) : SporStrong name p := by
  intro Y _ _ K B hC hN hS
  exact strong_of_centShapeMulti hGood hRk hOut hBr hP hIH hD hC hN hS
    (center_eq_bot_of_mult hSpM hC hS hm)

theorem sporStrong_of_goodSporMultiShape
    {name : TauCeti.SporadicName} {p : ℕ} {names : List TauCeti.SporadicName}
    (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds name p) (hm : ¬ p ∣ sporadicMultiplierOrder name)
    (hChev : ChevStrong p) (hSp : ∀ S ∈ names, SporStrong S p)
    (hD : CentShapeMulti p (GoodSpor p names) (RkSpor p names) (NativeSporadic.Carrier name)) :
    SporStrong name p :=
  sporStrong_of_centShapeMulti (fun _ _ _ _ e h => GoodSpor.of_equiv e h)
    (fun _ _ _ _ e h => RkSpor.of_equiv e h) hOut hSpM hBr hP hm
    (fun _ _ _ _ _ h hG hR => strong_goodSpor hChev hSp h hG hR) hD

end Template

end CFSG.HardMathSupport.Dickson.I271
