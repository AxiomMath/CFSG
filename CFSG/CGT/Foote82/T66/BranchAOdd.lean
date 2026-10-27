module

public import CFSG.CGT.Foote82.T66.MC1Steps
import CFSG.CGT.Foote82.Lemma64
import CFSG.GH74.Uniqueness.SU.SU10Fusion
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CoverDihedral
import CFSG.Quasithin.Background.G11Bridge
import CFSG.CGT.Foote82.T66.Overgroup
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.CGT.Foote82.BranchAAux

open CFSG.Open CFSG.Quasithin.G11

section Dihedral

variable {K : Type*} [Group K]

private theorem pow_val_intCast {ρ : K} {N : ℕ} [NeZero N] (hρ : ρ ^ N = 1) (k : ℤ) :
    ρ ^ (k : ZMod N).val = ρ ^ k := by
  rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, ZMod.val_intCast]
  exact (Int.mod_modEq k N).of_dvd (by exact_mod_cast orderOf_dvd_of_pow_eq_one hρ)

private theorem pow_val_eq_zpow {ρ : K} {N : ℕ} [NeZero N] (hρ : ρ ^ N = 1) (i : ZMod N) (k : ℤ)
    (hk : (k : ZMod N) = i) : ρ ^ i.val = ρ ^ k := by
  rw [← hk, pow_val_intCast hρ]

private def dihMap (a ρ : K) (N : ℕ) : DihedralGroup N → K
  | .r i => ρ ^ i.val
  | .sr i => a * ρ ^ i.val

private theorem dihMap_mul {a ρ : K} {N : ℕ} [NeZero N] (ha : a * a = 1)
    (haρ : ∀ k : ℤ, a * ρ ^ k = ρ ^ (-k) * a) (hρ : ρ ^ N = 1) (x y : DihedralGroup N) :
    dihMap a ρ N (x * y) = dihMap a ρ N x * dihMap a ρ N y := by
  have hv : ∀ i : ZMod N, ρ ^ i.val = ρ ^ (i.val : ℤ) := fun i => (zpow_natCast ρ _).symm
  have hadd : ∀ i j : ZMod N, ρ ^ (i + j).val = ρ ^ i.val * ρ ^ j.val := fun i j => by
    rw [pow_val_eq_zpow hρ (i + j) ((i.val : ℤ) + j.val) (by push_cast; simp), zpow_add,
      zpow_natCast, zpow_natCast]
  have hsub : ∀ i j : ZMod N, ρ ^ (j - i).val = ρ ^ (-(i.val : ℤ)) * ρ ^ j.val := fun i j => by
    rw [pow_val_eq_zpow hρ (j - i) (-(i.val : ℤ) + j.val) (by push_cast; simp; ring), zpow_add,
      zpow_natCast]
  rcases x with i | i <;> rcases y with j | j
  · show ρ ^ (i + j).val = ρ ^ i.val * ρ ^ j.val
    exact hadd i j
  · show a * ρ ^ (j - i).val = ρ ^ i.val * (a * ρ ^ j.val)
    rw [hsub, hv i, ← mul_assoc, ← mul_assoc, haρ, neg_neg]
  · show a * ρ ^ (i + j).val = a * ρ ^ i.val * ρ ^ j.val
    rw [hadd, mul_assoc]
  · show ρ ^ (j - i).val = a * ρ ^ i.val * (a * ρ ^ j.val)
    rw [hsub, hv i, ← mul_assoc, haρ, mul_assoc (ρ ^ _) a a, ha, mul_one]

private def dihHom (a ρ : K) (N : ℕ) [NeZero N] (ha : a * a = 1)
    (haρ : ∀ k : ℤ, a * ρ ^ k = ρ ^ (-k) * a) (hρ : ρ ^ N = 1) : DihedralGroup N →* K where
  toFun := dihMap a ρ N
  map_one' := by
    show ρ ^ (0 : ZMod N).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' := dihMap_mul ha haρ hρ

theorem nonempty_closure_mulEquiv_dihedral [Finite K] {a b : K} (ha : a * a = 1)
    (hb : b * b = 1) {N : ℕ} (hN : orderOf (a * b) = N) (h3 : 3 ≤ N) :
    Nonempty (Subgroup.closure ({a, b} : Set K) ≃* DihedralGroup N) := by
  have : NeZero N := ⟨by omega⟩
  set ρ := a * b with hρdef
  have hρN : ρ ^ N = 1 := by rw [← hN]; exact pow_orderOf_eq_one ρ
  have hconj := CFSG.QuasithinUnique.Ch1.involution_conj_zpow ha hb
  have haρ : ∀ k : ℤ, a * ρ ^ k = ρ ^ (-k) * a := fun k => by
    calc a * ρ ^ k = (a * ρ ^ k * a) * a := by rw [mul_assoc (a * ρ ^ k), ha, mul_one]
      _ = ρ ^ (-k) * a := by rw [hconj]
  let f := dihHom a ρ N ha haρ hρN
  have hfr : ∀ i : ZMod N, f (.r i) = ρ ^ i.val := fun _ => rfl
  have hfsr : ∀ i : ZMod N, f (.sr i) = a * ρ ^ i.val := fun _ => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro (i | i) hi
    · rw [hfr] at hi
      have h1 : orderOf ρ ∣ i.val := orderOf_dvd_of_pow_eq_one hi
      rw [hN] at h1
      have h2 : i.val < N := ZMod.val_lt i
      have h3 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt h1 h2
      rw [ZMod.val_eq_zero] at h3
      rw [h3, DihedralGroup.one_def]
    · exfalso
      rw [hfsr] at hi
      have haeq : a = (ρ ^ i.val)⁻¹ := eq_inv_of_mul_eq_one_left hi
      have hcomm : a * ρ = ρ * a := by
        rw [haeq]
        exact ((Commute.refl ρ).pow_left _).inv_left.eq
      have h2 : ρ ^ 2 = 1 := by
        have h := haρ 1
        rw [zpow_one, zpow_neg, zpow_one, hcomm] at h
        have h' : ρ = ρ⁻¹ := mul_right_cancel h
        rw [pow_two]
        nth_rewrite 2 [h']
        exact mul_inv_cancel ρ
      have := orderOf_le_of_pow_eq_one (by norm_num) h2
      omega
  have hrange : f.range = Subgroup.closure ({a, b} : Set K) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      have haC : a ∈ Subgroup.closure ({a, b} : Set K) := Subgroup.subset_closure (by simp)
      have hbC : b ∈ Subgroup.closure ({a, b} : Set K) := Subgroup.subset_closure (by simp)
      have hρC : ρ ∈ Subgroup.closure ({a, b} : Set K) := Subgroup.mul_mem _ haC hbC
      rcases x with i | i
      · exact Subgroup.pow_mem _ hρC _
      · exact Subgroup.mul_mem _ haC (Subgroup.pow_mem _ hρC _)
    · intro g hg
      rcases CFSG.QuasithinUnique.Ch1.mem_closure_involutions_cases ha hb hg with
        ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exact ⟨.r (k : ZMod N), by rw [hfr, pow_val_intCast hρN]⟩
      · refine ⟨.sr ((-k : ℤ) : ZMod N), ?_⟩
        rw [hfsr, pow_val_intCast hρN, haρ, neg_neg]
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

end Dihedral

section Involutions

variable {Q : Type*} [Group Q]

theorem inv_mul_zpow {a b : Q} (ha : a * a = 1) (hb : b * b = 1) (k : ℤ) :
    a * (a * b) ^ k = (a * b) ^ (-k) * a := by
  calc a * (a * b) ^ k = (a * (a * b) ^ k * a) * a := by
        rw [mul_assoc (a * (a * b) ^ k), ha, mul_one]
    _ = (a * b) ^ (-k) * a := by rw [CFSG.QuasithinUnique.Ch1.involution_conj_zpow ha hb]

theorem commute_pow_half {a b : Q} (ha : a * a = 1) (hb : b * b = 1) {k : ℕ}
    (hk : (a * b) ^ (2 * k) = 1) : a * (a * b) ^ k = (a * b) ^ k * a := by
  have h := inv_mul_zpow ha hb k
  rw [zpow_natCast, zpow_neg, zpow_natCast] at h
  rw [h]
  congr 1
  rw [inv_eq_iff_mul_eq_one, ← pow_add, ← two_mul, hk]

theorem sq_eq_one_of_eq_pow {a b : Q} (hb : b * b = 1) (ha : a * a = 1) {k : ℕ}
    (h : a = (a * b) ^ k) : (a * b) ^ 2 = 1 := by
  have key : ∀ c : Q, c = (a * b) ^ k → c * (a * b) = (a * b) * c := fun c hc => by
    rw [hc]
    exact ((Commute.refl (a * b)).pow_left k).eq
  have hc := key a h
  have hb' : a * b * a = b := by
    calc a * b * a = a * (a * b) := hc.symm
      _ = b := by rw [← mul_assoc, ha, one_mul]
  rw [pow_two]
  calc a * b * (a * b) = (a * b * a) * b := by group
    _ = 1 := by rw [hb', hb]

theorem exists_orderOf_eq_two_pow {g : Q} {n : ℕ} (hg : g ^ (2 ^ n) = 1) :
    ∃ k, orderOf g = 2 ^ k := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hg)
  exact ⟨k, hk⟩

theorem isPGroup_closure_of_involutions {a b : Q} (ha : a * a = 1) (hb : b * b = 1) {n : ℕ}
    (hn : orderOf (a * b) = 2 ^ n) : IsPGroup 2 (Subgroup.closure ({a, b} : Set Q)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  rw [Subgroup.orderOf_mk]
  have hρ : (a * b) ^ (2 ^ n) = 1 := by rw [← hn]; exact pow_orderOf_eq_one _
  rcases CFSG.QuasithinUnique.Ch1.mem_closure_involutions_cases ha hb hg with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · refine exists_orderOf_eq_two_pow (n := n) ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hρ, one_zpow]
  · refine exists_orderOf_eq_two_pow (n := 1) ?_
    rw [pow_one, pow_two]
    calc (a * b) ^ i * a * ((a * b) ^ i * a) = (a * b) ^ i * (a * (a * b) ^ i) * a := by group
      _ = (a * b) ^ i * ((a * b) ^ (-i) * a) * a := by rw [inv_mul_zpow ha hb]
      _ = 1 := by rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul, ha]

end Involutions

section StdFormFacts

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L : Subgroup (GLV V)} {z : GLV V}

theorem z_mem_G (h : StdForm G L z) : z ∈ G :=
  h.extremal.setup.S_le (Subgroup.mem_zpowers z)

theorem L_le_G (h : StdForm G L z) : L ≤ G :=
  h.extremal.L_le

theorem z_mem_cent (h : StdForm G L z) : z ∈ Subgroup.centralizer (L : Set (GLV V)) :=
  Subgroup.mem_centralizer_iff.2 fun l hl =>
    ((Subgroup.mem_centralizer_iff.1 (h.extremal.setup.component.1 hl).2) z
      (Subgroup.mem_zpowers z)).symm

theorem z_mem_K (h : StdForm G L z) : z ∈ G ⊓ Subgroup.centralizer (L : Set (GLV V)) :=
  ⟨z_mem_G h, z_mem_cent h⟩

theorem z_mul_z (h : StdForm G L z) : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rwa [h.orderOf_s, pow_two] at this

theorem quasisimple_L (h : StdForm G L z) : CFSG.Open.IsQuasisimple ↥L :=
  h.extremal.setup.component.2.2

theorem perfect_L (h : StdForm G L z) : ⁅L, L⁆ = L :=
  commutator_eq_self_of_isQuasisimple (quasisimple_L h)

theorem mem_map_conj_iff {Γ : Type*} [Group Γ] {H : Subgroup Γ} {g x : Γ} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [mul_assoc]⟩

theorem conj_mem_K {x c : GLV V} (hxG : x ∈ G)
    (hxN : x ∈ Subgroup.normalizer (L : Set (GLV V)))
    (hc : c ∈ G ⊓ Subgroup.centralizer (L : Set (GLV V))) :
    x * c * x⁻¹ ∈ G ⊓ Subgroup.centralizer (L : Set (GLV V)) := by
  refine Subgroup.mem_inf.2 ⟨G.mul_mem (G.mul_mem hxG (Subgroup.mem_inf.1 hc).1) (G.inv_mem hxG),
    Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
  have hl' : x⁻¹ * l * x ∈ L := (Subgroup.mem_normalizer_iff''.1 hxN l).1 hl
  have hcl := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 _ hl'
  calc l * (x * c * x⁻¹) = x * ((x⁻¹ * l * x) * c) * x⁻¹ := by group
    _ = x * (c * (x⁻¹ * l * x)) * x⁻¹ := by rw [hcl]
    _ = x * c * x⁻¹ * l := by group

theorem cent_le_normalizer (h : StdForm G L z) :
    ∀ a ∈ G ⊓ Subgroup.centralizer (L : Set (GLV V)), orderOf a = 2 →
      G ⊓ Subgroup.centralizer ({a} : Set (GLV V)) ≤ Subgroup.normalizer (L : Set (GLV V)) := by
  intro a ha hao g hg
  by_contra hgN
  have hodd := h.tight g (Subgroup.mem_inf.1 hg).1 hgN
  have hgaa : g * a * g⁻¹ = a := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).2, mul_inv_cancel_right]
  have haK : a ∈ (G ⊓ Subgroup.centralizer (L : Set (GLV V))).map (MulAut.conj g).toMonoidHom := by
    rw [mem_map_conj_iff]
    have : g⁻¹ * a * g = a := by
      calc g⁻¹ * a * g = g⁻¹ * (g * a * g⁻¹) * g := by rw [hgaa]
        _ = a := by group
    rw [this]
    exact ha
  have hdvd := orderOf_dvd_natCard (⟨a, Subgroup.mem_inf.2 ⟨ha, haK⟩⟩ :
    ↥((G ⊓ Subgroup.centralizer (L : Set (GLV V))) ⊓
      (G ⊓ Subgroup.centralizer (L : Set (GLV V))).map (MulAut.conj g).toMonoidHom))
  rw [Subgroup.orderOf_mk, hao] at hdvd
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

theorem not_le_normalizer (h : StdForm G L z) :
    ¬ G ≤ Subgroup.normalizer (L : Set (GLV V)) := by
  intro hGN
  have hS := h.extremal.setup
  have hcl : normalClosure G L ≤ L := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, l, hl, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (hGN hγ) l).1 hl
  have hGle : G ≤ L ⊔ Subgroup.zpowers z := hS.gen.le.trans (sup_le_sup_right hcl _)
  have hLN : L ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup (GLV V)) : Set (GLV V)) :=
    (hS.component.1.trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  have hbot := hS.eq_bot_of_isPGroup hS.S_le hS.isPGroup
    (hGle.trans (sup_le hLN Subgroup.le_normalizer))
  exact h.extremal.S_ne_bot hbot

theorem exists_not_mem_normalizer (h : StdForm G L z) :
    ∃ g ∈ G, g ∉ Subgroup.normalizer (L : Set (GLV V)) := by
  by_contra hne
  exact not_le_normalizer h fun g hg => by
    by_contra hgN
    exact hne ⟨g, hg, hgN⟩

theorem commutator_eq_bot_of_le_inf {Γ : Type*} [Group Γ] [Finite Γ] {L M : Subgroup Γ}
    (hL : CFSG.Open.IsQuasisimple ↥L) (hcard : Nat.card M = Nat.card L) (hne : M ≠ L)
    (hLM : ⁅L, M⁆ ≤ L ⊓ M) : ⁅L, M⁆ = ⊥ := by
  have hLq : CFSG.IsQuasisimple ↥L :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
      ↥L).1 hL
  have hLnM : ∀ l ∈ L, ∀ m ∈ M, l * m * l⁻¹ ∈ M := by
    intro l hl m hm
    have hc : l * m * l⁻¹ * m⁻¹ ∈ M := (hLM (Subgroup.commutator_mem_commutator hl hm)).2
    have : l * m * l⁻¹ = (l * m * l⁻¹ * m⁻¹) * m := by group
    rw [this]
    exact M.mul_mem hc hm
  have hN : ((L ⊓ M).subgroupOf L).Normal := by
    constructor
    intro x hx l
    refine ⟨L.mul_mem (L.mul_mem l.2 hx.1) (L.inv_mem l.2), ?_⟩
    exact hLnM l l.2 x hx.2
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq hN with htop | hcen
  · exfalso
    apply hne
    have hLleM : L ≤ M := by
      intro l hl
      have : (⟨l, hl⟩ : ↥L) ∈ (L ⊓ M).subgroupOf L := by rw [htop]; trivial
      exact this.2
    exact (Subgroup.eq_of_le_of_card_ge hLleM (le_of_eq hcard)).symm
  · have hperf : Group.IsPerfect ↥L := hLq.1
    refine CFSG.LocalCores.perfect_double_commutator hperf ?_
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro c hc l hl
    have hcLM := hLM hc
    have hcen' : (⟨c, hcLM.1⟩ : ↥L) ∈ Subgroup.center ↥L := hcen hcLM
    have hcomm := Subgroup.mem_center_iff.1 hcen' ⟨l, hl⟩
    have : c * l = l * c := congrArg Subtype.val hcomm.symm
    rw [Subgroup.mem_bot, commutatorElement_def, this]
    group

theorem not_commutator_le_inf (h : StdForm G L z) :
    ∀ g ∈ G, g ∉ Subgroup.normalizer (L : Set (GLV V)) →
      ¬ ⁅L, L.map (MulAut.conj g⁻¹).toMonoidHom⁆ ≤ L ⊓ L.map (MulAut.conj g⁻¹).toMonoidHom := by
  intro g hg hgN hle
  have hcard : Nat.card (L.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card L :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hne : L.map (MulAut.conj g⁻¹).toMonoidHom ≠ L := by
    intro heq
    apply hgN
    have hginv : g⁻¹ ∈ Subgroup.normalizer (L : Set (GLV V)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro l
      constructor
      · intro hl
        rw [← heq]
        exact ⟨l, hl, rfl⟩
      · intro hl
        rw [← heq] at hl
        obtain ⟨l', hl', hll'⟩ := hl
        have : l' = l := by
          have h1 := congrArg (fun x => g * x * g⁻¹) hll'
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
          group at h1
          exact h1
        rw [← this]
        exact hl'
    simpa using Subgroup.inv_mem _ hginv
  exact h.commutator_ne_bot g⁻¹ (G.inv_mem hg)
    (commutator_eq_bot_of_le_inf (quasisimple_L h) hcard hne hle)

theorem fix_commSpace (h : StdForm G L z) :
    ∀ x ∈ G ⊓ Subgroup.centralizer (L : Set (GLV V)), orderOf x = 2 →
      ∀ v ∈ commSpace (Subgroup.zpowers x) ⊤, ∀ d ∈ L, d v = v := by
  intro x hx hxo v hv d hd
  have hp : IsPGroup 2 (Subgroup.zpowers x) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  exact (CFSG.CGT.Foote82.lemma61 (perfect_L h) h.extremal.setup.irrTilde
    (fun l hl => (Subgroup.mem_centralizer_iff.1 hx.2 l hl)) hp).1 d hd v hv

end StdFormFacts

section Rank

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L : Subgroup (GLV V)} {z : GLV V}

theorem orderOf_conj_eq {Γ : Type*} [Group Γ] (k x : Γ) : orderOf (k * x * k⁻¹) = orderOf x := by
  have := MulEquiv.orderOf_eq (MulAut.conj k) x
  rwa [MulAut.conj_apply] at this

theorem eq_of_commute_of_pRank_one {K : Subgroup (GLV V)} (hK : CFSG.Open.pRank 2 K = 1) {a b : GLV V}
    (ha : a ∈ K) (hb : b ∈ K) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hab : a * b = b * a) :
    a = b := by
  by_contra hne
  have := CFSG.GH74.Uniqueness.SU.SU10.two_le_pRank_of_commuting_involutions ha hb ha2 hb2 hne hab
  omega

theorem eq_of_isPGroup_of_pRank_one {K P : Subgroup (GLV V)} (hK : CFSG.Open.pRank 2 K = 1) (hPK : P ≤ K)
    (hP : IsPGroup 2 P) {a b : GLV V} (ha : a ∈ P) (hb : b ∈ P) (ha2 : orderOf a = 2)
    (hb2 : orderOf b = 2) : a = b :=
  CFSG.GH74.Uniqueness.SU.SU10.eq_of_orderOf_two_of_pRank_le_one hP
    ((CFSG.SectionRank.pRank_mono Nat.one_lt_two hPK).trans hK.le) ha hb ha2 hb2

theorem exists_conj_of_pRank_one {K : Subgroup (GLV V)} (hK : CFSG.Open.pRank 2 K = 1) {a b : GLV V}
    (ha : a ∈ K) (hb : b ∈ K) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) :
    ∃ k ∈ K, b = k * a * k⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a' : ↥K := ⟨a, ha⟩
  set b' : ↥K := ⟨b, hb⟩
  have ha2' : orderOf a' = 2 := by rw [Subgroup.orderOf_mk]; exact ha2
  have hb2' : orderOf b' = 2 := by rw [Subgroup.orderOf_mk]; exact hb2
  have hpa : IsPGroup 2 (Subgroup.zpowers a') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha2', pow_one])
  have hpb : IsPGroup 2 (Subgroup.zpowers b') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2', pow_one])
  obtain ⟨P, hP⟩ := hpa.exists_le_sylow
  obtain ⟨R, hR⟩ := hpb.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥K P R
  have hmem : k * a' * k⁻¹ ∈ (R : Subgroup ↥K) := by
    rw [← hk, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hP (Subgroup.mem_zpowers a'))
  have hRmap : IsPGroup 2 ((R : Subgroup ↥K).map K.subtype) := R.isPGroup'.map K.subtype
  have hka : orderOf (((k * a' * k⁻¹ : ↥K) : GLV V)) = 2 := by
    rw [Subgroup.orderOf_coe, orderOf_conj_eq, ha2']
  have heq := eq_of_isPGroup_of_pRank_one hK (Subgroup.map_subtype_le _) hRmap
    (a := ((k * a' * k⁻¹ : ↥K) : GLV V)) (b := b) ⟨_, hmem, rfl⟩
    ⟨b', hR (Subgroup.mem_zpowers b'), rfl⟩ hka hb2
  exact ⟨k, k.2, by rw [← heq]; rfl⟩

theorem norm_of_branchA (h : StdForm G L z)
    (hrank : CFSG.Open.pRank 2 (G ⊓ Subgroup.centralizer (L : Set (GLV V))) = 1)
    (hA : ∀ v ∈ commSpace (Subgroup.zpowers z) ⊤, v ≠ 0 →
      G ⊓ vFix v ≤ Subgroup.normalizer (L : Set (GLV V))) :
    ∀ x ∈ G ⊓ Subgroup.centralizer (L : Set (GLV V)), orderOf x = 2 →
      ∀ v ∈ commSpace (Subgroup.zpowers x) ⊤, v ≠ 0 →
        ∀ g ∈ G, g v = v → g ∈ Subgroup.normalizer (L : Set (GLV V)) := by
  intro x hx hxo v hv hv0 g hg hgv
  obtain ⟨k, hk, rfl⟩ := exists_conj_of_pRank_one hrank (z_mem_K h) hx h.orderOf_s hxo
  have hkG : k ∈ G := (Subgroup.mem_inf.1 hk).1
  have hv' : k⁻¹ v ∈ commSpace (Subgroup.zpowers z) ⊤ := by
    rw [commSpace_zpowers_top] at hv ⊢
    obtain ⟨u, rfl⟩ := hv
    refine ⟨k⁻¹ u, ?_⟩
    simp
  have hv0' : k⁻¹ v ≠ 0 := by
    intro h0
    apply hv0
    have := congrArg k h0
    simpa using this
  have hmem : k⁻¹ * g * k ∈ G ⊓ vFix (k⁻¹ v) := by
    refine Subgroup.mem_inf.2 ⟨G.mul_mem (G.mul_mem (G.inv_mem hkG) hg) hkG, ?_⟩
    show (k⁻¹ * g * k) (k⁻¹ v) = k⁻¹ v
    simp [hgv]
  have hN := hA (k⁻¹ v) hv' hv0' hmem
  have hkN : k ∈ Subgroup.normalizer (L : Set (GLV V)) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.1 hk).2
  have : g = k * (k⁻¹ * g * k) * k⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hkN hN) (Subgroup.inv_mem _ hkN)

theorem false_of_normalizer (h : StdForm G L z)
    (hrank : CFSG.Open.pRank 2 (G ⊓ Subgroup.centralizer (L : Set (GLV V))) = 1) {x : GLV V}
    (hxG : x ∈ G) (hxN : x ∈ Subgroup.normalizer (L : Set (GLV V))) (hx2 : x * x = 1) {a : ℕ}
    (ha : 2 ≤ a) (hord : orderOf (z * x) = 2 ^ a) : False := by
  have hz2 := z_mul_z h
  have hzK := z_mem_K h
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hw := conj_mem_K hxG hxN hzK
  have hzw : z * (x * z * x⁻¹) = (z * x) ^ 2 := by
    rw [hxinv, pow_two]
    group
  have hρ2K : (z * x) ^ 2 ∈ G ⊓ Subgroup.centralizer (L : Set (GLV V)) := by
    rw [← hzw]
    exact Subgroup.mul_mem _ hzK hw
  have hpow : 2 * 2 ^ (a - 2) = 2 ^ (a - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hpow' : 2 * 2 ^ (a - 1) = 2 ^ a := by
    rw [← pow_succ']
    congr 1
    omega
  have huK : (z * x) ^ (2 ^ (a - 1)) ∈ G ⊓ Subgroup.centralizer (L : Set (GLV V)) := by
    rw [← hpow, pow_mul]
    exact Subgroup.pow_mem _ hρ2K _
  have hu2 : orderOf ((z * x) ^ (2 ^ (a - 1))) = 2 := by
    have h2a : 2 ∣ orderOf (z * x) := by
      rw [hord]
      exact dvd_pow_self 2 (by omega)
    have := orderOf_pow_orderOf_div (x := z * x) (n := 2) (by rw [hord]; positivity) h2a
    rwa [hord, ← hpow', Nat.mul_div_cancel_left _ (by norm_num)] at this
  have hzu : z * (z * x) ^ (2 ^ (a - 1)) = (z * x) ^ (2 ^ (a - 1)) * z := by
    refine commute_pow_half hz2 hx2 ?_
    rw [hpow', ← hord]
    exact pow_orderOf_eq_one _
  have hne : (z * x) ^ (2 ^ (a - 1)) ≠ z := by
    intro hu
    have hsq := sq_eq_one_of_eq_pow hx2 hz2 hu.symm
    have hdvd := orderOf_dvd_of_pow_eq_one hsq
    rw [hord] at hdvd
    have h1 := Nat.le_of_dvd (by norm_num) hdvd
    have h2 : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    omega
  exact hne (eq_of_commute_of_pRank_one hrank huK hzK hu2 h.orderOf_s hzu.symm)

theorem conj_mem_normalizer_of_mem {L : Subgroup (GLV V)} {k z : GLV V}
    (hz : z ∈ Subgroup.normalizer
      ((L.map (MulAut.conj k⁻¹).toMonoidHom : Subgroup (GLV V)) : Set (GLV V))) :
    k * z * k⁻¹ ∈ Subgroup.normalizer (L : Set (GLV V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro l
  have h1 := (Subgroup.mem_normalizer_iff.1 hz) (k⁻¹ * l * k)
  rw [mem_map_conj_iff, mem_map_conj_iff] at h1
  simp only [inv_inv] at h1
  have e1 : k * (k⁻¹ * l * k) * k⁻¹ = l := by group
  have e2 : k * (z * (k⁻¹ * l * k) * z⁻¹) * k⁻¹ = k * z * k⁻¹ * l * (k * z * k⁻¹)⁻¹ := by group
  rw [e1, e2] at h1
  exact h1

theorem oddTransp_pair (h : StdForm G L z)
    (hrank : CFSG.Open.pRank 2 (G ⊓ Subgroup.centralizer (L : Set (GLV V))) = 1)
    (hA : ∀ v ∈ commSpace (Subgroup.zpowers z) ⊤, v ≠ 0 →
      G ⊓ vFix v ≤ Subgroup.normalizer (L : Set (GLV V))) {g : GLV V} (hg : g ∈ G) :
    orderOf (z * (g * z * g⁻¹)) ≤ 2 ∨ Odd (orderOf (z * (g * z * g⁻¹))) := by
  have hz2 := z_mul_z h
  have hzK := z_mem_K h
  have hy2 : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := by
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hyG : g * z * g⁻¹ ∈ G := G.mul_mem (G.mul_mem hg (z_mem_G h)) (G.inv_mem hg)
  have H64 := fun (k : GLV V) (hk : k ∈ G) => CFSG.CGT.Foote82.lemma64 (L_le_G h)
    (cent_le_normalizer h) (not_commutator_le_inf h) (fix_commSpace h)
    (norm_of_branchA h hrank hA) hzK h.orderOf_s hzK h.orderOf_s hk
  obtain ⟨a, b, hb, hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (z * (g * z * g⁻¹))).ne'
  rcases Nat.lt_or_ge a 2 with ha | ha
  · interval_cases a
    · right
      rw [hm, pow_zero, one_mul]
      exact hb
    · by_cases hb1 : b = 1
      · left
        rw [hm, hb1]
        norm_num
      · exfalso
        have hb3 : 3 ≤ b := by
          obtain ⟨c, rfl⟩ := hb
          omega
        have hord : orderOf (z * (g * z * g⁻¹)) = 2 * b := by rw [hm, pow_one]
        obtain ⟨φ⟩ := nonempty_closure_mulEquiv_dihedral hz2 hy2 hord (by omega)
        have key := (H64 g⁻¹ (G.inv_mem hg)).2 b hb (by omega)
        simp only [inv_inv] at key
        have hyC := key ⟨φ.trans (MulEquiv.refl _)⟩
        have hyK : g * z * g⁻¹ ∈ G ⊓ Subgroup.centralizer (L : Set (GLV V)) :=
          Subgroup.mem_inf.2 ⟨hyG, hyC⟩
        have hρK : z * (g * z * g⁻¹) ∈ G ⊓ Subgroup.centralizer (L : Set (GLV V)) :=
          Subgroup.mul_mem _ hzK hyK
        have huK := Subgroup.pow_mem _ hρK b
        have hu2 : orderOf ((z * (g * z * g⁻¹)) ^ b) = 2 := by
          have := orderOf_pow_orderOf_div (x := z * (g * z * g⁻¹)) (n := 2)
            (by rw [hord]; omega) (by rw [hord]; exact dvd_mul_right 2 b)
          rwa [hord, Nat.mul_div_cancel_left _ (by norm_num)] at this
        have hzu := commute_pow_half hz2 hy2 (k := b) (by rw [← hord]; exact pow_orderOf_eq_one _)
        have hne : (z * (g * z * g⁻¹)) ^ b ≠ z := by
          intro hu
          have hsq := sq_eq_one_of_eq_pow hy2 hz2 hu.symm
          have hdvd := orderOf_dvd_of_pow_eq_one hsq
          rw [hord] at hdvd
          have := Nat.le_of_dvd (by norm_num) hdvd
          omega
        exact hne (eq_of_commute_of_pRank_one hrank huK hzK hu2 h.orderOf_s hzu.symm)
  · exfalso
    obtain ⟨c, hc⟩ := hb
    set ρ := z * (g * z * g⁻¹) with hρ
    have hρG : ρ ∈ G := G.mul_mem (z_mem_G h) hyG
    have hhG : g⁻¹ * ρ ^ c ∈ G := G.mul_mem (G.inv_mem hg) (G.pow_mem hρG c)
    have hyρ : g * z * g⁻¹ = z * ρ := by
      rw [hρ, ← mul_assoc, hz2, one_mul]
    have hzc : (ρ ^ c)⁻¹ * z = z * ρ ^ c := by
      have := inv_mul_zpow hz2 hy2 (c : ℤ)
      rw [← hρ, zpow_natCast, zpow_neg, zpow_natCast] at this
      exact this.symm
    have hy' : (g⁻¹ * ρ ^ c)⁻¹ * z * (g⁻¹ * ρ ^ c) = z * ρ ^ b := by
      calc (g⁻¹ * ρ ^ c)⁻¹ * z * (g⁻¹ * ρ ^ c) = (ρ ^ c)⁻¹ * (g * z * g⁻¹) * ρ ^ c := by group
        _ = (ρ ^ c)⁻¹ * z * ρ * ρ ^ c := by rw [hyρ, mul_assoc ((ρ ^ c)⁻¹) z ρ]
        _ = z * ρ ^ c * ρ * ρ ^ c := by rw [hzc]
        _ = z * ρ ^ b := by
          rw [hc, mul_assoc z, mul_assoc z, ← pow_succ, ← pow_add]
          congr 2
          omega
    have hρb : orderOf (ρ ^ b) = 2 ^ a := by
      have := orderOf_pow_orderOf_div (x := ρ) (n := 2 ^ a) (orderOf_pos ρ).ne'
        (by rw [hm]; exact dvd_mul_right _ _)
      rwa [hm, Nat.mul_div_cancel_left _ (by positivity)] at this
    have hy'2 : z * ρ ^ b * (z * ρ ^ b) = 1 := by
      rw [← hy']
      calc (g⁻¹ * ρ ^ c)⁻¹ * z * (g⁻¹ * ρ ^ c) * ((g⁻¹ * ρ ^ c)⁻¹ * z * (g⁻¹ * ρ ^ c)) =
          (g⁻¹ * ρ ^ c)⁻¹ * (z * z) * (g⁻¹ * ρ ^ c) := by group
        _ = 1 := by rw [hz2]; group
    have hzy' : z * (z * ρ ^ b) = ρ ^ b := by rw [← mul_assoc, hz2, one_mul]
    have hp : IsPGroup 2 (Subgroup.closure ({z, z * ρ ^ b} : Set (GLV V))) :=
      isPGroup_closure_of_involutions hz2 hy'2 (by rw [hzy']; exact hρb)
    have key := (H64 (g⁻¹ * ρ ^ c) hhG).1
    rw [hy'] at key
    rcases key hp with hN | hN
    · have hy'G : z * ρ ^ b ∈ G := G.mul_mem (z_mem_G h) (G.pow_mem hρG b)
      exact false_of_normalizer h hrank hy'G hN hy'2 ha (by rw [hzy']; exact hρb)
    · have hxN := conj_mem_normalizer_of_mem hN
      have hxG : (g⁻¹ * ρ ^ c) * z * (g⁻¹ * ρ ^ c)⁻¹ ∈ G :=
        G.mul_mem (G.mul_mem hhG (z_mem_G h)) (G.inv_mem hhG)
      have hx2 : (g⁻¹ * ρ ^ c) * z * (g⁻¹ * ρ ^ c)⁻¹ * ((g⁻¹ * ρ ^ c) * z * (g⁻¹ * ρ ^ c)⁻¹) = 1 := by
        calc (g⁻¹ * ρ ^ c) * z * (g⁻¹ * ρ ^ c)⁻¹ * ((g⁻¹ * ρ ^ c) * z * (g⁻¹ * ρ ^ c)⁻¹) =
            (g⁻¹ * ρ ^ c) * (z * z) * (g⁻¹ * ρ ^ c)⁻¹ := by group
          _ = 1 := by rw [hz2]; group
      have hconj : z * ((g⁻¹ * ρ ^ c) * z * (g⁻¹ * ρ ^ c)⁻¹) =
          (g⁻¹ * ρ ^ c) * ((z * ρ ^ b) * z) * (g⁻¹ * ρ ^ c)⁻¹ := by
        rw [← hy']
        group
      have hyz : orderOf ((z * ρ ^ b) * z) = 2 ^ a := by
        have hinv : (z * ρ ^ b) * z = (z * (z * ρ ^ b))⁻¹ := by
          rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hy'2, inv_eq_of_mul_eq_one_right hz2]
        rw [hinv, orderOf_inv, hzy', hρb]
      exact false_of_normalizer h hrank hxG hxN hx2 ha
        (by rw [hconj, orderOf_conj_eq, hyz])

theorem oddTransp (h : StdForm G L z)
    (hrank : CFSG.Open.pRank 2 (G ⊓ Subgroup.centralizer (L : Set (GLV V))) = 1)
    (hA : ∀ v ∈ commSpace (Subgroup.zpowers z) ⊤, v ≠ 0 →
      G ⊓ vFix v ≤ Subgroup.normalizer (L : Set (GLV V))) :
    ∀ g ∈ G, ∀ k ∈ G, orderOf ((g * z * g⁻¹) * (k * z * k⁻¹)) ≤ 2 ∨
      Odd (orderOf ((g * z * g⁻¹) * (k * z * k⁻¹))) := by
  intro g hg k hk
  have e : (g * z * g⁻¹) * (k * z * k⁻¹) = g * (z * ((g⁻¹ * k) * z * (g⁻¹ * k)⁻¹)) * g⁻¹ := by
    group
  rw [e, orderOf_conj_eq]
  exact oddTransp_pair h hrank hA (G.mul_mem (G.inv_mem hg) hk)

end Rank

end CFSG.CGT.Foote82.BranchAAux
