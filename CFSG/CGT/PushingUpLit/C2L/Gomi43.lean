module

public import CFSG.CGT.PushingUpLit.C2L.Gomi42
public import CFSG.CGT.PushingUpLit.C2L.Gomi34

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2KSW
open CFSG.RankThree.PartOne (omegaOneCenterIn)
open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_normalizer_of_comm {Q X : Subgroup G} (h : ∀ x ∈ X, ∀ y ∈ Q, y * x = x * y) :
    Q ≤ Subgroup.normalizer (X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 : ∀ x ∈ X, g * x * g⁻¹ = x := fun x hx => by rw [h x hx g hg]; group
  have h2 : ∀ x ∈ X, g⁻¹ * x * g = x := fun x hx => by rw [h x hx g⁻¹ (inv_mem hg)]; group
  constructor
  · intro hx
    rw [h1 x hx]
    exact hx
  · intro hx
    have := h2 _ hx
    rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
    rw [this]
    exact hx

theorem comm_mem {Q : Subgroup G} {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) : ⁅a, b⁆ ∈ Q := by
  rw [commutatorElement_def]
  exact Q.mul_mem (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha)) (Q.inv_mem hb)

theorem mem_of_mem_normalizer_of_pow [Finite G] {K S : Subgroup G} (hS : IsSylowOf 2 S K) {w : G}
    (hwK : w ∈ K) (hwn : w ∈ Subgroup.normalizer (S : Set G)) (hw2 : ∃ j : ℕ, w ^ 2 ^ j = 1) :
    w ∈ S := by
  obtain ⟨Q, hQ⟩ := hS
  obtain ⟨j, hj⟩ := hw2
  have hw'j : (⟨w, hwK⟩ : ↥K) ^ 2 ^ j = 1 := Subtype.ext (by simpa using hj)
  have hp : IsPGroup 2 (Subgroup.zpowers (⟨w, hwK⟩ : ↥K)) := by
    rintro ⟨y, hy⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    refine ⟨j, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw'j, one_zpow]
  have hw'n : (⟨w, hwK⟩ : ↥K) ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro c
    have h1 := Subgroup.mem_normalizer_iff.1 hwn (c : G)
    rw [← hQ] at h1
    have e1 : (c : G) ∈ Subgroup.map K.subtype (Q : Subgroup K) ↔ c ∈ (Q : Subgroup K) :=
      Subgroup.mem_map_iff_mem K.subtype_injective
    have e2 : w * (c : G) * w⁻¹ ∈ Subgroup.map K.subtype (Q : Subgroup K) ↔
        (⟨w, hwK⟩ * c * ⟨w, hwK⟩⁻¹ : ↥K) ∈ (Q : Subgroup K) :=
      Subgroup.mem_map_iff_mem K.subtype_injective (x := (⟨w, hwK⟩ * c * ⟨w, hwK⟩⁻¹ : ↥K))
    exact e1.symm.trans (h1.trans e2)
  have h2 := hp.inf_normalizer_sylow Q
  have hmem : (⟨w, hwK⟩ : ↥K) ∈ Subgroup.zpowers (⟨w, hwK⟩ : ↥K) ⊓ (Q : Subgroup K) := by
    rw [← h2]
    exact ⟨Subgroup.mem_zpowers _, hw'n⟩
  rw [← hQ]
  exact ⟨_, hmem.2, rfl⟩

@[expose] def commHom (Q : Subgroup G) (hQ : ClassLETwo Q) (x : G) (hx : x ∈ Q) : ↥Q →* G where
  toFun y := ⁅(y : G), x⁆
  map_one' := by simp
  map_mul' y y' := by
    have e1 : ⁅(y : G) * y', x⁆ = (y : G) * ⁅(y' : G), x⁆ * (y : G)⁻¹ * ⁅(y : G), x⁆ := by
      simp only [commutatorElement_def]; group
    have h1 : ⁅(y' : G), x⁆ * (y : G) = (y : G) * ⁅(y' : G), x⁆ :=
      commutatorElement_eq_one_iff_mul_comm.1 (hQ (y' : G) y'.2 x hx (y : G) y.2)
    have h2 : ⁅(y : G), x⁆ * ⁅(y' : G), x⁆ = ⁅(y' : G), x⁆ * ⁅(y : G), x⁆ :=
      commutatorElement_eq_one_iff_mul_comm.1
        (hQ (y : G) y.2 x hx ⁅(y' : G), x⁆ (comm_mem y'.2 hx))
    have h3 : (y : G) * ⁅(y' : G), x⁆ * (y : G)⁻¹ = ⁅(y' : G), x⁆ := by
      rw [← h1]; group
    show ⁅(y : G) * y', x⁆ = ⁅(y : G), x⁆ * ⁅(y' : G), x⁆
    rw [e1, h3]
    exact h2.symm

theorem dihedral_mem {N D : Subgroup G} (hDN : N ≤ Subgroup.normalizer (D : Set G)) {a b g : G}
    (hg : g = a * b) (haN : a ∈ N) (hbN : b ∈ N) (ha : a * a ∈ D) (hb : b * b ∈ D) (k : ℕ) :
    a * g ^ k * a⁻¹ * g ^ k ∈ D ∧ b * g ^ k * b⁻¹ * g ^ k ∈ D := by
  have hgN : g ∈ N := hg ▸ N.mul_mem haN hbN
  have hconj : ∀ d ∈ D, g⁻¹ * d * g ∈ D := fun d hd =>
    (Subgroup.mem_normalizer_iff''.1 (hDN hgN) d).1 hd
  have hd0a : a * g * a⁻¹ * g ∈ D := by
    have e : a * g * a⁻¹ * g = a * a * (b * b) := by rw [hg]; group
    rw [e]
    exact D.mul_mem ha hb
  have hd0b : b * g * b⁻¹ * g ∈ D := by
    have e : b * g * b⁻¹ * g = (b * (a * a) * b⁻¹) * (b * b) := by rw [hg]; group
    rw [e]
    exact D.mul_mem ((Subgroup.mem_normalizer_iff.1 (hDN hbN) _).1 ha) hb
  induction k with
  | zero => simp [D.one_mem]
  | succ k ih =>
    obtain ⟨iha, ihb⟩ := ih
    constructor
    · have e : a * g ^ (k + 1) * a⁻¹ * g ^ (k + 1) =
          (a * g * a⁻¹ * g) * (g⁻¹ * (a * g ^ k * a⁻¹ * g ^ k) * g) := by group
      rw [e]
      exact D.mul_mem hd0a (hconj _ iha)
    · have e : b * g ^ (k + 1) * b⁻¹ * g ^ (k + 1) =
          (b * g * b⁻¹ * g) * (g⁻¹ * (b * g ^ k * b⁻¹ * g ^ k) * g) := by group
      rw [e]
      exact D.mul_mem hd0b (hconj _ ihb)

section Finite

variable [Finite G]

theorem mem_normalizer_of_comm_mod {P D S : Subgroup G} (hP : IsSylowOf 2 P ⊤) (hD : GomiD P D)
    (hS : IsSylowOf 2 S (Subgroup.normalizer (D : Set G))) {a w : G} (haS : a ∈ S) (haD : a ∉ D)
    (hwN : w ∈ Subgroup.normalizer (D : Set G)) (hwa : w * a * w⁻¹ * a⁻¹ ∈ D) :
    w ∈ Subgroup.normalizer (S : Set G) := by
  have hNw : (Subgroup.normalizer (D : Set G)).map (MulAut.conj w).toMonoidHom =
      Subgroup.normalizer (D : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hwN)
  have hSw : IsSylowOf 2 (S.map (MulAut.conj w).toMonoidHom) (Subgroup.normalizer (D : Set G)) := by
    have := (isSylowOf_map_conj_iff (A := S) (B := Subgroup.normalizer (D : Set G)) w).2 hS
    rwa [hNw] at this
  by_contra hwn
  have hne : S.map (MulAut.conj w).toMonoidHom ≠ S := fun heq =>
    hwn (Subgroup.mem_normalizer_iff_map_conj_eq.2 heq)
  have hTI := hD.inf_eq hP hS hSw hne.symm
  have hDS : D ≤ S := hD.1.1.oTwoIn_eq ▸ oTwoIn_le_of_isSylowOf hS
  have hmem : w * a * w⁻¹ ∈ S ⊓ S.map (MulAut.conj w).toMonoidHom := by
    refine ⟨?_, ⟨a, haS, by simp [MulAut.conj_apply]⟩⟩
    have e : w * a * w⁻¹ = (w * a * w⁻¹ * a⁻¹) * a := by group
    rw [e]
    exact S.mul_mem (hDS hwa) haS
  rw [hTI] at hmem
  apply haD
  have := (Subgroup.mem_normalizer_iff''.1 hwN (w * a * w⁻¹)).1 hmem
  simpa [mul_assoc] using this

end Finite

namespace Side

variable [Finite G] {P P' D : Subgroup G}

theorem not_omega_le (hA : GomiAmbient G) (h : Side P P' D) :
    ¬ omegaOneCenterIn (P ⊓ Subgroup.normalizer (D : Set G)) ≤
      omegaOneCenterIn (P' ⊓ Subgroup.normalizer (D : Set G)) := by
  intro hX
  have hQs := h.isSylowOf_inf_normalizer
  have hQ's := h.symm.isSylowOf_inf_normalizer
  have hDQ := h.lt_normalizer
  have hDQ' := h.symm.lt_normalizer
  have hQne := h.inf_normalizer_ne
  have hXne : omegaOneCenterIn (P ⊓ Subgroup.normalizer (D : Set G)) ≠ ⊥ :=
    omegaOneCenterIn_ne_bot hQs.isPGroup hDQ.ne_bot
  have hXp : IsPGroup 2 (omegaOneCenterIn (P ⊓ Subgroup.normalizer (D : Set G))) :=
    hQs.isPGroup.to_le (omegaOneCenterIn_le _)
  have hQX : P ⊓ Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (omegaOneCenterIn (P ⊓ Subgroup.normalizer (D : Set G)) : Set G) :=
    le_normalizer_of_comm fun x hx y hy => (mem_omegaOneCenterIn_iff.1 hx).2.1 y hy
  have hQ'X : P' ⊓ Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer (omegaOneCenterIn (P ⊓ Subgroup.normalizer (D : Set G)) : Set G) :=
    le_normalizer_of_comm fun x hx y hy => (mem_omegaOneCenterIn_iff.1 (hX hx)).2.1 y hy
  have hK : CFSG.Assembly.IsTwoLocal
      (Subgroup.normalizer (omegaOneCenterIn (P ⊓ Subgroup.normalizer (D : Set G)) : Set G)) :=
    ⟨_, hXne, hXp, rfl⟩
  have h1 : D < P ⊓ Subgroup.normalizer
      (omegaOneCenterIn (P ⊓ Subgroup.normalizer (D : Set G)) : Set G) :=
    hDQ.trans_le (le_inf inf_le_left hQX)
  have h2 : D < P' ⊓ Subgroup.normalizer
      (omegaOneCenterIn (P ⊓ Subgroup.normalizer (D : Set G)) : Set G) :=
    hDQ'.trans_le (le_inf inf_le_left hQ'X)
  obtain ⟨-, -, hPK, -⟩ := h.inf_le_normalizer hA hK h1 h2
  have hPKQ : P ⊓ Subgroup.normalizer
      (omegaOneCenterIn (P ⊓ Subgroup.normalizer (D : Set G)) : Set G) =
        P ⊓ Subgroup.normalizer (D : Set G) := le_antisymm hPK (le_inf inf_le_left hQX)
  have hPQ : P ≤ P ⊓ Subgroup.normalizer (D : Set G) := by
    by_contra hnle
    have hlt : P ⊓ Subgroup.normalizer (D : Set G) < P := lt_of_le_not_ge inf_le_left hnle
    have h3 := lt_inf_normalizer_of_lt h.sylow.isPGroup hlt
    exact h3.not_ge ((inf_le_inf_left P (normalizer_le_normalizer_omegaOneCenterIn _)).trans
      hPKQ.le)
  have hPeq : P = P ⊓ Subgroup.normalizer (D : Set G) := le_antisymm hPQ inf_le_left
  have hcl : ClassLETwo (P ⊓ Subgroup.normalizer (D : Set G)) :=
    hA.classLETwo_of_le h.isTwoLocal h.hH.not_twoClosed hQs.le hQs.isPGroup
  have hcP : ClassLETwo P := by
    rw [hPeq]
    exact hcl
  have hZ := hA.zElem P h.sylow hcP
  have hZle : (P ⊓ Subgroup.normalizer (D : Set G)) ⊓
        Subgroup.centralizer ((P ⊓ Subgroup.normalizer (D : Set G) : Subgroup G) : Set G) ≤
      (P' ⊓ Subgroup.normalizer (D : Set G)) ⊓
        Subgroup.centralizer ((P' ⊓ Subgroup.normalizer (D : Set G) : Subgroup G) : Set G) := by
    intro z hz
    have hz1 : z ∈ P ⊓ Subgroup.centralizer (P : Set G) := by
      rw [← hPeq] at hz
      exact hz
    have hzX : z ∈ omegaOneCenterIn (P ⊓ Subgroup.normalizer (D : Set G)) :=
      mem_omegaOneCenterIn_iff.2 ⟨hz.1, fun y hy => (Subgroup.mem_centralizer_iff.1 hz.2 y hy),
        hZ z hz1⟩
    obtain ⟨hz'Q, hz'c, -⟩ := mem_omegaOneCenterIn_iff.1 (hX hzX)
    exact ⟨hz'Q, Subgroup.mem_centralizer_iff.2 hz'c⟩
  have hN : Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer (oTwoIn (Subgroup.normalizer (D : Set G)) : Set G) ≤
        oTwoIn (Subgroup.normalizer (D : Set G)) := by
    rw [h.hH.oTwoIn_eq]
    exact inf_le_right.trans (h.centralizer_le hA)
  exact prop34_not_le hN hQs hQ's hcl hQne hZle

theorem inf_centralizer_eq (hA : GomiAmbient G) (h : Side P P' D) {x : G}
    (hx : x ∈ omegaOneCenterIn (P ⊓ Subgroup.normalizer (D : Set G)))
    (hx' : x ∉ omegaOneCenterIn (P' ⊓ Subgroup.normalizer (D : Set G))) :
    P' ⊓ Subgroup.centralizer ({x} : Set G) = D := by
  obtain ⟨hxQ, hxc, hx2⟩ := mem_omegaOneCenterIn_iff.1 hx
  have hDQ : D ≤ P ⊓ Subgroup.normalizer (D : Set G) := h.le_inf_normalizer
  have hxD : x ∈ D := h.omega_le hA hDQ hx
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hx' (Subgroup.one_mem _)
  have hDC : D ≤ P' ⊓ Subgroup.centralizer ({x} : Set G) := by
    refine le_inf h.le' fun d hd => ?_
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    rw [Set.mem_singleton_iff.1 hy]
    exact (hxc d (hDQ hd)).symm
  refine le_antisymm ?_ hDC
  by_contra hnle
  have hlt : D < P' ⊓ Subgroup.centralizer ({x} : Set G) := lt_of_le_not_ge hDC hnle
  have hK := isTwoLocal_centralizer_of_mul_self hx1 hx2
  have hQK : P ⊓ Subgroup.normalizer (D : Set G) ≤ P ⊓ Subgroup.centralizer ({x} : Set G) := by
    refine le_inf inf_le_left fun y hy => ?_
    refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
    rw [Set.mem_singleton_iff.1 hz]
    exact (hxc y hy).symm
  have h1 : D < P ⊓ Subgroup.centralizer ({x} : Set G) := h.lt_normalizer.trans_le hQK
  obtain ⟨hs1, hs2, hle1, hle2⟩ := h.inf_le_normalizer hA hK h1 hlt
  have heq1 : P ⊓ Subgroup.centralizer ({x} : Set G) = P ⊓ Subgroup.normalizer (D : Set G) :=
    le_antisymm hle1 hQK
  have hcard : Nat.card ↥(P' ⊓ Subgroup.centralizer ({x} : Set G)) =
      Nat.card ↥(P' ⊓ Subgroup.normalizer (D : Set G)) := by
    calc Nat.card ↥(P' ⊓ Subgroup.centralizer ({x} : Set G))
        = Nat.card ↥(P ⊓ Subgroup.centralizer ({x} : Set G)) := by
          rw [hs1.card_eq, hs2.card_eq]
      _ = Nat.card ↥(P ⊓ Subgroup.normalizer (D : Set G)) := by rw [heq1]
      _ = Nat.card ↥(P' ⊓ Subgroup.normalizer (D : Set G)) := by
          rw [h.isSylowOf_inf_normalizer.card_eq, h.symm.isSylowOf_inf_normalizer.card_eq]
  have heq2 : P' ⊓ Subgroup.centralizer ({x} : Set G) = P' ⊓ Subgroup.normalizer (D : Set G) :=
    Subgroup.eq_of_le_of_card_ge hle2 hcard.ge
  refine hx' (mem_omegaOneCenterIn_iff.2 ⟨h.symm.le_inf_normalizer hxD, fun y hy => ?_, hx2⟩)
  have hy' : y ∈ P' ⊓ Subgroup.centralizer ({x} : Set G) := heq2.symm ▸ hy
  exact (Subgroup.mem_centralizer_iff.1 hy'.2 x (Set.mem_singleton x)).symm

theorem exists_commHom (hA : GomiAmbient G) (h : Side P P' D) {x : G}
    (hx : x ∈ omegaOneCenterIn (P ⊓ Subgroup.normalizer (D : Set G)))
    (hx' : x ∉ omegaOneCenterIn (P' ⊓ Subgroup.normalizer (D : Set G))) :
    ∃ f : ↥(P' ⊓ Subgroup.normalizer (D : Set G)) →* G,
      (∀ y : ↥(P' ⊓ Subgroup.normalizer (D : Set G)), f y = ⁅(y : G), x⁆) ∧
      f.range ≤ omegaOneCenterIn (P' ⊓ Subgroup.normalizer (D : Set G)) ∧
      f.ker = D.subgroupOf (P' ⊓ Subgroup.normalizer (D : Set G)) := by
  have hQ's := h.symm.isSylowOf_inf_normalizer
  have hcl : ClassLETwo (P' ⊓ Subgroup.normalizer (D : Set G)) :=
    hA.classLETwo_of_le h.isTwoLocal h.hH.not_twoClosed hQ's.le hQ's.isPGroup
  obtain ⟨hxQ, hxc, hx2⟩ := mem_omegaOneCenterIn_iff.1 hx
  have hxD : x ∈ D := h.omega_le hA h.le_inf_normalizer hx
  have hxQ' : x ∈ P' ⊓ Subgroup.normalizer (D : Set G) := h.symm.le_inf_normalizer hxD
  refine ⟨commHom _ hcl x hxQ', fun y => rfl, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    show ⁅(y : G), x⁆ ∈ omegaOneCenterIn (P' ⊓ Subgroup.normalizer (D : Set G))
    have hy : ⁅(y : G), x⁆ ∈ P' ⊓ Subgroup.normalizer (D : Set G) := comm_mem y.2 hxQ'
    refine mem_omegaOneCenterIn_iff.2 ⟨hy, fun c hc => ?_, ?_⟩
    · exact (commutatorElement_eq_one_iff_mul_comm.1 (hcl (y : G) y.2 x hxQ' c hc)).symm
    · have hzc : ⁅(y : G), x⁆ * x = x * ⁅(y : G), x⁆ :=
        commutatorElement_eq_one_iff_mul_comm.1 (hcl (y : G) y.2 x hxQ' x hxQ')
      have e : ⁅(y : G), x * x⁆ = ⁅(y : G), x⁆ * (x * ⁅(y : G), x⁆ * x⁻¹) := by
        simp only [commutatorElement_def]; group
      have e2 : x * ⁅(y : G), x⁆ * x⁻¹ = ⁅(y : G), x⁆ := by
        rw [← hzc]; group
      rw [hx2, e2] at e
      simpa using e.symm
  · ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show ⁅(y : G), x⁆ = 1 ↔ (y : G) ∈ D
    constructor
    · intro hy
      have hy1 : (y : G) ∈ P' ⊓ Subgroup.centralizer ({x} : Set G) := by
        refine ⟨y.2.1, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
        rw [Set.mem_singleton_iff.1 hz]
        exact (commutatorElement_eq_one_iff_mul_comm.1 hy).symm
      rwa [h.inf_centralizer_eq hA hx hx'] at hy1
    · intro hy
      exact commutatorElement_eq_one_iff_mul_comm.2 (hxc _ (h.le_inf_normalizer hy))

theorem comm_eq_one (hA : GomiAmbient G) (h : Side P P' D) {x : G}
    (hx : x ∈ omegaOneCenterIn (P ⊓ Subgroup.normalizer (D : Set G)))
    (hx' : x ∉ omegaOneCenterIn (P' ⊓ Subgroup.normalizer (D : Set G))) {a : G}
    (ha : a ∈ P' ⊓ Subgroup.normalizer (D : Set G))
    (hc : ⁅a, x⁆ ∈ omegaOneCenterIn (P ⊓ Subgroup.normalizer (D : Set G))) : ⁅a, x⁆ = 1 := by
  by_contra hc1
  obtain ⟨f, hf, hfr, hfk⟩ := h.exists_commHom hA hx hx'
  have hQs := h.isSylowOf_inf_normalizer
  have hQ's := h.symm.isSylowOf_inf_normalizer
  obtain ⟨hxQ, hxc, hx2⟩ := mem_omegaOneCenterIn_iff.1 hx
  have hDQ : D ≤ P ⊓ Subgroup.normalizer (D : Set G) := h.le_inf_normalizer
  obtain ⟨c, hcdef⟩ : ∃ c, c = ⁅a, x⁆ := ⟨_, rfl⟩
  rw [← hcdef] at hc hc1
  have hcX' : c ∈ omegaOneCenterIn (P' ⊓ Subgroup.normalizer (D : Set G)) := by
    rw [hcdef]
    exact hfr ⟨⟨a, ha⟩, hf ⟨a, ha⟩⟩
  obtain ⟨-, hccQ, hc2⟩ := mem_omegaOneCenterIn_iff.1 hc
  obtain ⟨-, hccQ', -⟩ := mem_omegaOneCenterIn_iff.1 hcX'
  have haD : a ∉ D := by
    intro haD
    apply hc1
    rw [hcdef]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hxc a (hDQ haD))
  have haa : a * a ∈ D := by
    have h1 : f (⟨a, ha⟩ * ⟨a, ha⟩) = 1 := by
      rw [map_mul, hf]
      simpa [hcdef] using hc2
    have h2 : (⟨a, ha⟩ * ⟨a, ha⟩ : ↥(P' ⊓ Subgroup.normalizer (D : Set G))) ∈ f.ker := h1
    rw [hfk] at h2
    exact Subgroup.mem_subgroupOf.1 h2
  obtain ⟨n, hnN, hQn⟩ := exists_eq_map_conj_of_isSylowOf hQ's hQs
  obtain ⟨b, hbdef⟩ : ∃ b, b = n * a * n⁻¹ := ⟨_, rfl⟩
  have hbQ : b ∈ P ⊓ Subgroup.normalizer (D : Set G) := by
    rw [hQn]
    exact ⟨a, ha, by rw [hbdef]; simp [MulAut.conj_apply]⟩
  have hnD : ∀ d, d ∈ D ↔ n * d * n⁻¹ ∈ D := Subgroup.mem_normalizer_iff.1 hnN
  have hbD : b ∉ D := fun hb => haD ((hnD a).2 (by rw [← hbdef]; exact hb))
  have hbb : b * b ∈ D := by
    have e : b * b = n * (a * a) * n⁻¹ := by rw [hbdef]; group
    rw [e]
    exact (hnD _).1 haa
  obtain ⟨g, hgdef⟩ : ∃ g, g = a * b := ⟨_, rfl⟩
  have haN : a ∈ Subgroup.normalizer (D : Set G) := ha.2
  have hbN : b ∈ Subgroup.normalizer (D : Set G) := hbQ.2
  have hgN : g ∈ Subgroup.normalizer (D : Set G) := by
    rw [hgdef]
    exact mul_mem haN hbN
  have hbx : b * x = x * b := hxc b hbQ
  have hax : a * x * a⁻¹ = c * x := by rw [hcdef, commutatorElement_def]; group
  have hgx : g * x * g⁻¹ = c * x := by
    calc g * x * g⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by rw [hgdef]; group
      _ = a * x * a⁻¹ := by rw [hbx]; group
      _ = c * x := hax
  have hbc : b * c = c * b := hccQ b hbQ
  have hac : a * c = c * a := hccQ' a ha
  have hgc : g * c = c * g := by
    calc g * c = a * (b * c) := by rw [hgdef]; group
      _ = a * (c * b) := by rw [hbc]
      _ = (a * c) * b := by group
      _ = (c * a) * b := by rw [hac]
      _ = c * g := by rw [hgdef]; group
  have hgxc : c = ⁅g, x⁆ := by
    rw [commutatorElement_def, hgx]; group
  have hpow := pow_mul_mul_pow_inv_eq hgxc hgc
  have hex : ∃ k : ℕ, 0 < k ∧ g ^ k ∈ D :=
    ⟨orderOf g, orderOf_pos g, by rw [pow_orderOf_eq_one]; exact D.one_mem⟩
  classical
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = Nat.find hex := ⟨_, rfl⟩
  have hn₀spec : 0 < n₀ ∧ g ^ n₀ ∈ D := by
    rw [hn₀]
    exact Nat.find_spec hex
  have hmin : ∀ k, k < n₀ → 0 < k → g ^ k ∉ D := fun k hk hk0 hkD =>
    Nat.find_min hex (by rw [← hn₀]; exact hk) ⟨hk0, hkD⟩
  have heven : Even n₀ := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨j, hj⟩ := hodd
    have hcpow : c ^ n₀ = c := by
      rw [hj, pow_succ, pow_mul, sq, hc2, one_pow, one_mul]
    have hcomm : g ^ n₀ * x = x * g ^ n₀ := hxc _ (hDQ hn₀spec.2)
    have hD1 : g ^ n₀ * x * (g ^ n₀)⁻¹ = x := by rw [hcomm]; group
    have h3 := hpow n₀
    rw [hD1, hcpow] at h3
    apply hc1
    have h4 : c * x = 1 * x := by rw [one_mul]; exact h3.symm
    exact mul_right_cancel h4
  obtain ⟨m, hm⟩ := heven
  have hm0 : 0 < m := by have := hn₀spec.1; omega
  have hmlt : m < n₀ := by have := hn₀spec.1; omega
  obtain ⟨w, hwdef⟩ : ∃ w, w = g ^ m := ⟨_, rfl⟩
  have hwD : w ∉ D := by
    rw [hwdef]
    exact hmin m hmlt hm0
  have hww : w * w ∈ D := by
    rw [hwdef, ← pow_add, ← hm]
    exact hn₀spec.2
  have hwN : w ∈ Subgroup.normalizer (D : Set G) := by
    rw [hwdef]
    exact Subgroup.pow_mem _ hgN m
  obtain ⟨hda, hdb⟩ := dihedral_mem (N := Subgroup.normalizer (D : Set G)) (D := D) (le_refl _)
    hgdef haN hbN haa hbb m
  rw [← hwdef] at hda hdb
  have hwa : w * a * w⁻¹ * a⁻¹ ∈ D := by
    have e : w * a * w⁻¹ * a⁻¹ = (a * w * a⁻¹ * w * (w * w)⁻¹)⁻¹ := by group
    rw [e]
    exact D.inv_mem (D.mul_mem hda (D.inv_mem hww))
  have hwb : w * b * w⁻¹ * b⁻¹ ∈ D := by
    have e : w * b * w⁻¹ * b⁻¹ = (b * w * b⁻¹ * w * (w * w)⁻¹)⁻¹ := by group
    rw [e]
    exact D.inv_mem (D.mul_mem hdb (D.inv_mem hww))
  have hwn' := mem_normalizer_of_comm_mod h.sylow h.max hQ's ha haD hwN hwa
  have hwn := mem_normalizer_of_comm_mod h.sylow h.max hQs hbQ hbD hwN hwb
  have hw2 : ∃ j : ℕ, w ^ 2 ^ j = 1 := by
    obtain ⟨j, hj⟩ := h.hH.isPGroup ⟨w * w, hww⟩
    refine ⟨j + 1, ?_⟩
    have : (w * w) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    rw [pow_succ, pow_mul', sq]
    exact this
  have hwQ' := mem_of_mem_normalizer_of_pow hQ's hwN hwn' hw2
  have hwQ := mem_of_mem_normalizer_of_pow hQs hwN hwn hw2
  have hTI := h.max.inf_eq h.sylow hQs hQ's h.inf_normalizer_ne
  have hwTI : w ∈ (P ⊓ Subgroup.normalizer (D : Set G)) ⊓ (P' ⊓ Subgroup.normalizer (D : Set G)) :=
    ⟨hwQ, hwQ'⟩
  rw [hTI] at hwTI
  exact hwD hwTI

end Side

namespace Hyp42

variable [Finite G] {P D₁ D₂ Q₁ Q₂ P₁ P₂ : Subgroup G}

omit [Finite G] in
theorem inf_normalizer_eq (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂) :
    P ⊓ Subgroup.normalizer (D₁ : Set G) = P ⊓ Subgroup.normalizer (D₂ : Set G) :=
  h.pair.2.2.2.1

theorem not_omega_le₁' (hA : GomiAmbient G) (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂) :
    ¬ omegaOneCenterIn Q₁ ≤ omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G)) := by
  rw [h.side₁.eq_inf]
  exact h.side₁.side.symm.not_omega_le hA

theorem lemma45_one (hA : GomiAmbient G) (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂)
    (hX : ¬ omegaOneCenterIn Q₂ ≤ D₁) :
    omegaOneCenterIn Q₁ ⊓ D₂ =
      omegaOneCenterIn Q₁ ⊓ omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G)) := by
  have h1 := h.side₁.side
  have h2 := h.side₂.side
  have e1 := h.side₁.eq_inf
  have e2 := h.side₂.eq_inf
  have hN := h.inf_normalizer_eq
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxX₁, hxD₂⟩
    refine ⟨hxX₁, ?_⟩
    by_contra hxX
    have hC : P ⊓ Subgroup.centralizer ({x} : Set G) = D₁ :=
      h1.symm.inf_centralizer_eq hA (by rw [← e1]; exact hxX₁) hxX
    obtain ⟨y, hyX₂, hyD₁⟩ := IsConcreteLE.not_le_iff_exists.1 hX
    have hyD₂ : y ∈ D₂ := by
      refine h2.omega_le hA (R := Q₂) ?_ hyX₂
      rw [e2]
      exact h2.symm.le_inf_normalizer
    have hyP : y ∈ P := h2.le hyD₂
    have hxQ₂ : x ∈ Q₂ := by
      rw [e2]
      exact h2.symm.le_inf_normalizer hxD₂
    have hyc : y ∈ Subgroup.centralizer ({x} : Set G) := by
      refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
      rw [Set.mem_singleton_iff.1 hz]
      exact (mem_omegaOneCenterIn_iff.1 hyX₂).2.1 x hxQ₂
    have hyP' : y ∈ P ⊓ Subgroup.centralizer ({x} : Set G) := ⟨hyP, hyc⟩
    rw [hC] at hyP'
    exact hyD₁ hyP'
  · rintro x ⟨hxX₁, hxX⟩
    refine ⟨hxX₁, ?_⟩
    have hXD : omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G)) ≤ D₂ := by
      refine h2.omega_le hA ?_
      rw [hN]
      exact h2.le_inf_normalizer
    exact hXD hxX

theorem lemma45_three_mp (hA : GomiAmbient G) (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂)
    (h1 : omegaOneCenterIn Q₁ ≤ D₂) : omegaOneCenterIn Q₂ ≤ D₁ := by
  by_contra hX
  have h2 := lemma45_one hA h hX
  refine h.not_omega_le₁' hA fun x hx => ?_
  have hx' : x ∈ omegaOneCenterIn Q₁ ⊓ D₂ := ⟨hx, h1 hx⟩
  rw [h2] at hx'
  exact hx'.2

theorem lemma45_three (hA : GomiAmbient G) (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂) :
    omegaOneCenterIn Q₁ ≤ D₂ ↔ omegaOneCenterIn Q₂ ≤ D₁ :=
  ⟨lemma45_three_mp hA h, lemma45_three_mp hA h.swap⟩

end Hyp42

end CFSG.CGT.PushingUpLit.C2L
