module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop126
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma119
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Main
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3VBar

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

namespace Input183

variable {G : Type} [Group G]

theorem glaPLayer_le_self (p : ℕ) (C : Subgroup G) : GLAPLayer p C ≤ C :=
  sSup_le fun _ hL => hL.1

theorem gLBConj_le_centralizer_singleton {y g : G} {J : Subgroup G}
    (hg : g ∈ Subgroup.centralizer ({y} : Set G))
    (hJ : J ≤ Subgroup.centralizer ({y} : Set G)) :
    GLBConj g J ≤ Subgroup.centralizer ({y} : Set G) := by
  intro z hz
  rw [mem_gLBConj] at hz
  have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hJ hz)
  have h2 := Subgroup.mem_centralizer_singleton_iff.1 hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hgi : g⁻¹ * y = y * g⁻¹ := by
    calc g⁻¹ * y = g⁻¹ * (y * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * y) * g⁻¹ := by rw [h2]
      _ = y * g⁻¹ := by group
  calc z * y = g⁻¹ * (g * z * g⁻¹) * (g * y) := by group
    _ = g⁻¹ * (g * z * g⁻¹) * (y * g) := by rw [h2]
    _ = g⁻¹ * ((g * z * g⁻¹) * y) * g := by group
    _ = g⁻¹ * (y * (g * z * g⁻¹)) * g := by rw [h1]
    _ = (g⁻¹ * y) * (g * z * g⁻¹) * g := by group
    _ = (y * g⁻¹) * (g * z * g⁻¹) * g := by rw [hgi]
    _ = y * z := by group

theorem iSup_conj_layer_le_centralizer {p : ℕ} {y : G} {J : Subgroup G}
    (hJ : J ≤ Subgroup.centralizer ({y} : Set G)) :
    (⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({y} : Set G)), GLBConj g J) ≤
      Subgroup.centralizer ({y} : Set G) := by
  refine iSup₂_le fun g hg => gLBConj_le_centralizer_singleton ?_ hJ
  exact glaPLayer_le_self p _ hg

end Input183

theorem input18_3_2_holds : Prop126.Input18_3_2 := by
  intro p hp _ G _ _ _ _ _ x y _ _ hxy J hJ
  classical
  obtain ⟨hJT, -, -, -⟩ := id hJ
  have hJy : J ≤ Subgroup.centralizer ({y} : Set G) :=
    hJT.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Set.mem_insert_of_mem x rfl)))
  have hJx : J ≤ Subgroup.centralizer ({x} : Set G) :=
    hJT.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Set.mem_insert x {y})))
  have hKy := Input183.iSup_conj_layer_le_centralizer (p := p) hJy
  have hJK : J ≤ (⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({y} : Set G)), GLBConj g J) :=
    le_iSup₂_of_le (1 : G) (GLAPLayer p _).one_mem (le_of_eq (gLBConj_one J).symm)
  have hJS : J ≤ (⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({y} : Set G)), GLBConj g J) ⊓
      Subgroup.centralizer ({x} : Set G) := le_inf hJK hJx
  have hST : (⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({y} : Set G)), GLBConj g J) ⊓
      Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({x, y} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with rfl | rfl
    · exact (Subgroup.mem_centralizer_iff.1 hz.2) h (Set.mem_singleton h)
    · exact (Subgroup.mem_centralizer_iff.1 (hKy hz.1)) h (Set.mem_singleton h)
  exact glaPComponent_of_le hp hJ hJS hST

theorem input18_3Two_holds : Lemma1313.Input18_3Two := input18_3_2_holds


namespace Input183

variable {G : Type} [Group G]

def stab (L : Subgroup G) : Subgroup G where
  carrier := {g | GLBConj g L = L}
  one_mem' := gLBConj_one L
  mul_mem' := by
    intro a b ha hb
    show GLBConj (a * b) L = L
    have ha' : GLBConj a L = L := ha
    have hb' : GLBConj b L = L := hb
    calc GLBConj (a * b) L = GLBConj b (GLBConj a L) := (gLBConj_gLBConj b a L).symm
      _ = L := by rw [ha', hb']
  inv_mem' := by
    intro a ha
    show GLBConj a⁻¹ L = L
    have ha' : GLBConj a L = L := ha
    calc GLBConj a⁻¹ L = GLBConj a⁻¹ (GLBConj a L) := by rw [ha']
      _ = GLBConj (a * a⁻¹) L := gLBConj_gLBConj a⁻¹ a L
      _ = L := by rw [mul_inv_cancel, gLBConj_one]

theorem glaPComponent_ne_bot' {p : ℕ} [Finite G] {X K : Subgroup G} (hK : GLAPComponent p X K) :
    K ≠ ⊥ := by
  intro h
  subst h
  obtain ⟨-, -, hcomp, -⟩ := hK
  obtain ⟨-, hs⟩ := hcomp.2.2
  have hsub : Subsingleton (↥(((⊥ : Subgroup G).subgroupOf X).map
      (QuotientGroup.mk' (GLAPPrimeCore p ↥X)))) := by
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
    infer_instance
  exact (not_nontrivial_iff_subsingleton.2 inferInstance) hs.toNontrivial

end Input183

namespace Input183

theorem centralizer_pair_eq {G : Type} [Group G] (x y : G) :
    Subgroup.centralizer ({x, y} : Set G) =
      Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) := by
  ext z
  constructor
  · intro hz
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hz y (by simp)).symm,
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hz x (by simp)).symm⟩
  · intro hz
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with rfl | rfl
    · exact Subgroup.mem_centralizer_iff.1 h2 h (Set.mem_singleton h)
    · exact Subgroup.mem_centralizer_iff.1 h1 h (Set.mem_singleton h)


theorem gLBConj_centralizer_singleton_eq {G : Type} [Group G] {y g : G}
    (hg : g ∈ Subgroup.centralizer ({y} : Set G)) :
    GLBConj g (Subgroup.centralizer ({y} : Set G)) = Subgroup.centralizer ({y} : Set G) := by
  apply le_antisymm (Input183.gLBConj_le_centralizer_singleton hg le_rfl)
  have h := gLBConj_mono g (Input183.gLBConj_le_centralizer_singleton
    ((Subgroup.centralizer ({y} : Set G)).inv_mem hg) le_rfl)
  rwa [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one] at h

end Input183

theorem input18_3Gen_of_schreier
    (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier) :
    Prop115.Input18_3Gen := by
  intro p hp _ G _ _ hsimp hnab hkp x y hx hy hxy J hJ
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hJ' : GLAPComponent p (Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)) J := by
    have hcz : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
        Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hcz, ← Input183.centralizer_pair_eq x y]
    exact hJ
  have hxC : x ∈ Subgroup.centralizer ({y} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hxy
  have hEX : Subgroup.zpowers x ≤ Subgroup.centralizer ({y} : Set G) := Subgroup.zpowers_le.2 hxC
  have hE : CFSG.Open.IsElemAbelian p (Subgroup.zpowers x) :=
    CFSG.Open.isElemAbelian_zpowers (by rw [← hx]; exact pow_orderOf_eq_one x)
  have hne : Subgroup.centralizer ({y} : Set G) ≠ ⊤ := by
    intro htop
    have hmem : y ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer ({y} : Set G) := by
        rw [htop]
        exact Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.1 hg
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h0 | h0
    · rw [h0, Subgroup.mem_bot] at hmem
      rw [hmem, orderOf_one] at hy
      exact hp.one_lt.ne hy
    · obtain ⟨a, b, hab⟩ := hnab
      have ha : a ∈ Subgroup.center G := by
        rw [h0]
        exact Subgroup.mem_top a
      exact hab ((Subgroup.mem_center_iff.1 ha b).symm)
  have hK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({y} : Set G)) :=
    CFSG.KCore.KProperNonab.kGroupNonab CFSG.Open.isCatalogGroup_isoInvariant hkp _ hne
  obtain ⟨𝒞, h1, h2, h3, h4⟩ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.input18_3_4_of_schreier hS) G
      (Subgroup.centralizer ({y} : Set G)) hK p hp (Subgroup.zpowers x) hEX hE J hJ'
  have hJne : J ≠ ⊥ := Input183.glaPComponent_ne_bot' hJ
  have hJle : J ≤ ⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({y} : Set G)), GLBConj g J :=
    le_iSup₂_of_le (1 : G) (GLAPLayer p _).one_mem (le_of_eq (gLBConj_one J).symm)
  obtain ⟨L0, hL0⟩ : ∃ L0, L0 ∈ 𝒞 := by
    by_contra hno
    push_neg at hno
    have hbot : (⨆ L ∈ 𝒞, L) = ⊥ := by simp [hno]
    apply hJne
    rw [← h2, hbot] at hJle
    exact le_bot_iff.1 hJle
  by_cases hfix : GLBConj x L0 = L0
  ·
    left
    have hxs : x ∈ Input183.stab L0 := hfix
    have hzs : Subgroup.zpowers x ≤ Input183.stab L0 := Subgroup.zpowers_le.2 hxs
    have hLeq : ∀ L ∈ 𝒞, L = L0 := by
      intro L hL
      obtain ⟨e, he, hel⟩ := h4 L0 hL0 L hL
      have heS : GLBConj e L0 = L0 := hzs he
      rw [← hel]
      exact heS
    refine ⟨L0, h1 L0 hL0, ?_, hfix⟩
    rw [← h2]
    exact le_antisymm (iSup₂_le fun L hL => (hLeq L hL).le) (le_iSup₂_of_le L0 hL0 le_rfl)
  ·
    right
    have hpowC : ∀ k : ℕ, x ^ k ∈ Subgroup.centralizer ({y} : Set G) := fun k =>
      (Subgroup.centralizer ({y} : Set G)).pow_mem hxC k
    have hcomp : ∀ i : ZMod p,
        GLAPComponent p (Subgroup.centralizer ({y} : Set G)) (GLBConj (x ^ i.val) L0) := by
      intro i
      have h := glaPComponent_gLBConj (h1 L0 hL0) (x ^ i.val)
      rwa [Input183.gLBConj_centralizer_singleton_eq (hpowC _)] at h
    have hval : ∀ i : ZMod p, x ^ (i + 1).val = x ^ i.val * x := by
      intro i
      have h1' : (i + 1).val = (i.val + 1) % p := by
        rw [ZMod.val_add, ZMod.val_one]
      have h2' := pow_mod_orderOf (x := x) (n := i.val + 1)
      rw [hx] at h2'
      rw [h1', h2', pow_succ]
    have hconj_succ : ∀ i : ZMod p,
        GLBConj x (GLBConj (x ^ i.val) L0) = GLBConj (x ^ (i + 1).val) L0 := by
      intro i
      rw [gLBConj_gLBConj, hval]
    have hinj : Function.Injective (fun i : ZMod p => GLBConj (x ^ i.val) L0) := by
      intro i j hij
      have hij' : GLBConj (x ^ i.val) L0 = GLBConj (x ^ j.val) L0 := hij
      by_contra hne'
      have hdvd : ¬ ((p : ℤ) ∣ ((j.val : ℤ) - (i.val : ℤ))) := by
        intro hdvd
        apply hne'
        have h0 : (((j.val : ℤ) - (i.val : ℤ) : ℤ) : ZMod p) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hdvd
        push_cast at h0
        have hji : (j.val : ZMod p) = (i.val : ZMod p) := sub_eq_zero.1 h0
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hji
        exact hji.symm
      have hd_mem : x ^ ((j.val : ℤ) - (i.val : ℤ)) ∈ Input183.stab L0 := by
        rw [show x ^ ((j.val : ℤ) - (i.val : ℤ)) = x ^ j.val * (x ^ i.val)⁻¹ by
          rw [zpow_sub, zpow_natCast, zpow_natCast]]
        show GLBConj (x ^ j.val * (x ^ i.val)⁻¹) L0 = L0
        calc GLBConj (x ^ j.val * (x ^ i.val)⁻¹) L0
            = GLBConj (x ^ i.val)⁻¹ (GLBConj (x ^ j.val) L0) := (gLBConj_gLBConj _ _ _).symm
          _ = GLBConj (x ^ i.val)⁻¹ (GLBConj (x ^ i.val) L0) := by rw [← hij']
          _ = GLBConj (x ^ i.val * (x ^ i.val)⁻¹) L0 := gLBConj_gLBConj _ _ _
          _ = L0 := by rw [mul_inv_cancel, gLBConj_one]
      have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      obtain ⟨s, t, hst⟩ := (Irreducible.coprime_iff_not_dvd hpZ.irreducible).2 hdvd
      have hxp : x ^ (p : ℤ) = 1 := by
        rw [zpow_natCast, ← hx]
        exact pow_orderOf_eq_one x
      have hxeq : x = x ^ (t * ((j.val : ℤ) - (i.val : ℤ))) := by
        have hsum : t * ((j.val : ℤ) - (i.val : ℤ)) = 1 - (p : ℤ) * s := by linarith
        rw [hsum, zpow_sub, zpow_one, zpow_mul, hxp, one_zpow, inv_one, mul_one]
      apply hfix
      have hxS : x ∈ Input183.stab L0 := by
        have e : x ^ (t * ((j.val : ℤ) - (i.val : ℤ))) = (x ^ ((j.val : ℤ) - (i.val : ℤ))) ^ t := by
          rw [mul_comm, zpow_mul]
        rw [hxeq, e]
        exact (Input183.stab L0).zpow_mem hd_mem t
      exact hxS
    have hpow_val : ∀ k : ℤ, x ^ ((k : ZMod p).val) = x ^ k := by
      intro k
      have hv : (((k : ZMod p).val : ℕ) : ℤ) = k % (p : ℤ) := ZMod.val_intCast k
      have h3' := zpow_mod_orderOf x k
      rw [hx] at h3'
      calc x ^ (k : ZMod p).val = x ^ (((k : ZMod p).val : ℕ) : ℤ) := (zpow_natCast _ _).symm
        _ = x ^ (k % (p : ℤ)) := by rw [hv]
        _ = x ^ k := h3'
    refine ⟨fun i => GLBConj (x ^ i.val) L0, fun i => hcomp i, hinj, fun i => hconj_succ i, ?_⟩
    rw [← h2]
    apply le_antisymm
    · apply iSup₂_le
      intro L hL
      obtain ⟨e, he, hel⟩ := h4 L0 hL0 L hL
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 he
      refine le_iSup_of_le ((k : ZMod p)) (le_of_eq ?_)
      show L = GLBConj (x ^ ((k : ZMod p)).val) L0
      rw [← hel, ← hk, hpow_val k]
    · apply iSup_le
      intro i
      exact le_iSup₂_of_le (GLBConj (x ^ i.val) L0)
        (h3 L0 hL0 _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _)) le_rfl


namespace Input183

section Oprod

variable {H : Type} [Group H]

def oprod (n : ℕ) (f : ℕ → H) : H := ((List.range n).map f).prod

theorem oprod_zero (f : ℕ → H) : oprod 0 f = 1 := by
  simp [oprod]

theorem oprod_succ (n : ℕ) (f : ℕ → H) : oprod (n + 1) f = oprod n f * f n := by
  simp [oprod, List.range_succ]

theorem oprod_mem {S : Subgroup H} {n : ℕ} {f : ℕ → H} (h : ∀ j < n, f j ∈ S) :
    oprod n f ∈ S := by
  induction n with
  | zero => rw [oprod_zero]; exact S.one_mem
  | succ n ih =>
    rw [oprod_succ]
    exact S.mul_mem (ih fun j hj => h j (by omega)) (h n (by omega))

theorem commute_oprod {n : ℕ} {a : H} {f : ℕ → H} (h : ∀ j < n, Commute (f j) a) :
    Commute (oprod n f) a :=
  Subgroup.mem_centralizer_singleton_iff.1
    (oprod_mem (S := Subgroup.centralizer ({a} : Set H)) fun j hj =>
      Subgroup.mem_centralizer_singleton_iff.2 (h j hj))

theorem oprod_mul_of_comm {n : ℕ} {f g : ℕ → H}
    (h : ∀ j k, j < n → k < n → j ≠ k → Commute (f j) (g k)) :
    oprod n (fun j => f j * g j) = oprod n f * oprod n g := by
  induction n with
  | zero => rw [oprod_zero, oprod_zero, oprod_zero, mul_one]
  | succ n ih =>
    have ih' := ih (fun j k hj hk hjk => h j k (by omega) (by omega) hjk)
    have hc : Commute (oprod n g) (f n) :=
      commute_oprod (f := g) (a := f n) fun k hk =>
        (h n k (Nat.lt_succ_self n) (by omega) (by omega)).symm
    rw [oprod_succ, oprod_succ, oprod_succ, ih']
    simp only [mul_assoc]
    rw [← mul_assoc (oprod n g), hc.eq, mul_assoc]


end Oprod

section Oprod2

variable {H : Type} [Group H]

theorem oprod_congr {n : ℕ} {f g : ℕ → H} (h : ∀ j < n, f j = g j) : oprod n f = oprod n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [oprod_succ, oprod_succ, ih fun j hj => h j (by omega), h n (by omega)]

theorem oprod_ones (n : ℕ) : oprod n (fun _ => (1 : H)) = 1 := by
  induction n with
  | zero => exact oprod_zero _
  | succ n ih => rw [oprod_succ, ih, mul_one]

theorem oprod_single {n i : ℕ} {f : ℕ → H} (hi : i < n) (h : ∀ j < n, j ≠ i → f j = 1) :
    oprod n f = f i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [oprod_succ]
    by_cases hin : i = n
    · subst hin
      rw [oprod_congr (g := fun _ => 1) (fun j hj => h j (by omega) (by omega)), oprod_ones,
        one_mul]
    · rw [h n (by omega) (Ne.symm hin), mul_one]
      exact ih (by omega) fun j hj hji => h j (by omega) hji

theorem oprod_cons (n : ℕ) (f : ℕ → H) : oprod (n + 1) f = f 0 * oprod n (fun j => f (j + 1)) := by
  induction n with
  | zero => rw [oprod_succ, oprod_zero, oprod_zero, mul_one, one_mul]
  | succ n ih => rw [oprod_succ, ih, oprod_succ, mul_assoc]

theorem conj_oprod (g : H) (n : ℕ) (f : ℕ → H) :
    g * oprod n f * g⁻¹ = oprod n (fun j => g * f j * g⁻¹) := by
  induction n with
  | zero => rw [oprod_zero, oprod_zero, mul_one, mul_inv_cancel]
  | succ n ih =>
    rw [oprod_succ, oprod_succ, ← ih]
    simp only [mul_assoc, mul_inv_cancel_left]
    group

theorem oprod_rot (m : ℕ) (F : ℕ → H) (hper : ∀ k, F (k + (m + 1)) = F k)
    (hcomm : ∀ j k, j < m + 1 → k < m + 1 → j ≠ k → Commute (F j) (F k)) :
    oprod (m + 1) (fun j => F (j + m)) = oprod (m + 1) F := by
  rw [oprod_cons, oprod_succ]
  have h1 : (fun j => F (j + 1 + m)) = fun j => F (j + (m + 1)) := by
    funext j; congr 1; ring
  simp only [zero_add]
  rw [h1, show (fun j => F (j + (m + 1))) = F from funext hper]
  have hc : Commute (oprod m F) (F m) :=
    commute_oprod fun j hj => (hcomm j m (by omega) (by omega) (by omega))
  exact (hc.eq).symm ▸ rfl

end Oprod2

section Orbit

variable {Y : Type} [Group Y]

def orbA (b : Y) (X : Subgroup Y) (j : ℕ) : Subgroup Y := GLBConj (b ^ j)⁻¹ X

theorem orbA_zero (b : Y) (X : Subgroup Y) : orbA b X 0 = X := by
  simp [orbA, gLBConj_one]

theorem orbA_succ (b : Y) (X : Subgroup Y) (j : ℕ) :
    orbA b X (j + 1) = GLBConj b⁻¹ (orbA b X j) := by
  unfold orbA
  rw [gLBConj_gLBConj, pow_succ', mul_inv_rev]

theorem mem_orbA {b : Y} {X : Subgroup Y} {j : ℕ} {x : Y} (hx : x ∈ X) :
    b ^ j * x * (b ^ j)⁻¹ ∈ orbA b X j := by
  unfold orbA
  rw [mem_gLBConj]
  simpa [mul_assoc] using hx

theorem conj_mem_orbA_succ {b : Y} {X : Subgroup Y} {j : ℕ} {y : Y} (hy : y ∈ orbA b X j) :
    b * y * b⁻¹ ∈ orbA b X (j + 1) := by
  rw [orbA_succ, mem_gLBConj]
  simpa [mul_assoc] using hy

theorem orbA_add_period {b : Y} {X : Subgroup Y} {p : ℕ} (hbp : b ^ p = 1) (j : ℕ) :
    orbA b X (j + p) = orbA b X j := by
  unfold orbA
  rw [pow_add, hbp, mul_one]

theorem orbA_mod {b : Y} {X : Subgroup Y} {p : ℕ} (hb : orderOf b = p) (j : ℕ) :
    orbA b X (j % p) = orbA b X j := by
  unfold orbA
  rw [← hb, pow_mod_orderOf]


theorem orbit_factor {b : Y} {X : Subgroup Y} {p : ℕ}
    (hcomm : ∀ j k, j < p → k < p → j ≠ k → ∀ x ∈ orbA b X j, ∀ y ∈ orbA b X k, x * y = y * x)
    {g : Y} (hg : g ∈ ⨆ i : Fin p, orbA b X (i : ℕ)) :
    ∃ a : ℕ → Y, (∀ j < p, a j ∈ orbA b X j) ∧ g = oprod p a := by
  refine Subgroup.iSup_induction (S := fun i : Fin p => orbA b X (i : ℕ))
    (C := fun g => ∃ a : ℕ → Y, (∀ j < p, a j ∈ orbA b X j) ∧ g = oprod p a) hg ?_ ?_ ?_
  · intro i x hx
    refine ⟨fun j => if j = (i : ℕ) then x else 1, fun j hj => ?_, ?_⟩
    · by_cases hji : j = (i : ℕ)
      · simp only [hji, if_true]
        exact hx
      · simp only [hji, if_false]
        exact (orbA b X j).one_mem
    · rw [oprod_single i.isLt (fun j _ hji => if_neg hji), if_pos rfl]
  · exact ⟨fun _ => 1, fun j _ => (orbA b X j).one_mem, (oprod_ones p).symm⟩
  · rintro x y ⟨a, ha, rfl⟩ ⟨c, hc, rfl⟩
    refine ⟨fun j => a j * c j, fun j hj => (orbA b X j).mul_mem (ha j hj) (hc j hj), ?_⟩
    exact (oprod_mul_of_comm fun j k hj hk hjk => hcomm j k hj hk hjk _ (ha j hj) _ (hc k hk)).symm
      ▸ rfl

theorem block_uniq {L : Subgroup Y} {𝓛 : Set (Subgroup Y)} {b : Y} {X : Subgroup Y} {p : ℕ}
    (hL : L = sSup 𝓛)
    (h𝓛 : ∀ X₁ ∈ 𝓛, ∀ X₂ ∈ 𝓛, X₁ ≠ X₂ → ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x)
    (hmem : ∀ j < p, orbA b X j ∈ 𝓛) (hAL : ∀ j < p, orbA b X j ≤ L)
    (hAcomm : ∀ j k, j < p → k < p → j ≠ k → ∀ x ∈ orbA b X j, ∀ y ∈ orbA b X k, x * y = y * x)
    {a c : ℕ → Y} (ha : ∀ j < p, a j ∈ orbA b X j) (hc : ∀ j < p, c j ∈ orbA b X j)
    {z : Y} (hz : z ∈ L ⊓ Subgroup.centralizer (L : Set Y))
    (h : oprod p a = oprod p c * z) :
    ∀ j < p, (c j)⁻¹ * a j ∈ L ⊓ Subgroup.centralizer (L : Set Y) := by
  have hzc : ∀ y ∈ L, Commute y z := fun y hy =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2) y hy
  have U1 : ∀ d : ℕ → Y, (∀ j < p, d j ∈ orbA b X j) → ∀ j < p,
      ∃ w : Y, oprod p d = d j * w ∧ ∀ y ∈ orbA b X j, Commute w y := by
    intro d hd j hj
    set d' : ℕ → Y := fun k => if k = j then 1 else d k with hd'
    set e : ℕ → Y := fun k => if k = j then d j else 1 with he
    have hsplit : oprod p d = oprod p d' * d j := by
      have h1 : oprod p d = oprod p (fun k => d' k * e k) := oprod_congr fun k hk => by
        by_cases hkj : k = j
        · simp [hd', he, hkj]
        · simp [hd', he, hkj]
      have h2 : oprod p (fun k => d' k * e k) = oprod p d' * oprod p e := by
        refine oprod_mul_of_comm fun k k' hk hk' hkk' => ?_
        by_cases hk'j : k' = j
        · have hdk : d' k = d k := by simp [hd', show k ≠ j from fun h' => hkk' (h'.trans hk'j.symm)]
          have he' : e k' = d j := by simp [he, hk'j]
          rw [hdk, he']
          exact hAcomm k j hk hj (fun h' => hkk' (h'.trans hk'j.symm)) _ (hd k hk) _ (hd j hj)
        · have he' : e k' = 1 := by simp [he, hk'j]
          rw [he']
          exact Commute.one_right _
      have h3 : oprod p e = d j := by
        rw [oprod_single (f := e) hj (fun k _ hkj => by simp [he, hkj])]
        simp [he]
      rw [h1, h2, h3]
    have hcen : Commute (oprod p d') (d j) := by
      refine commute_oprod fun k hk => ?_
      by_cases hkj : k = j
      · simp [hd', hkj]
      · simp only [hd', hkj, if_false]
        show d k * d j = d j * d k
        exact hAcomm k j hk hj hkj _ (hd k hk) _ (hd j hj)
    refine ⟨oprod p d', ?_, ?_⟩
    · rw [hsplit]
      exact hcen.eq
    · intro y hy
      refine commute_oprod fun k hk => ?_
      by_cases hkj : k = j
      · simp [hd', hkj]
      · simp only [hd', hkj, if_false]
        exact hAcomm k j hk hj hkj _ (hd k hk) y hy
  intro j hj
  obtain ⟨wa, hwa, hwa'⟩ := U1 a ha j hj
  obtain ⟨wc, hwc, hwc'⟩ := U1 c hc j hj
  have e1 : a j * wa = c j * wc * z := by rw [← hwa, h, hwc]
  have key : (c j)⁻¹ * a j = wc * z * wa⁻¹ := by
    calc (c j)⁻¹ * a j = (c j)⁻¹ * (a j * wa) * wa⁻¹ := by group
      _ = (c j)⁻¹ * (c j * wc * z) * wa⁻¹ := by rw [e1]
      _ = wc * z * wa⁻¹ := by group
  set u := (c j)⁻¹ * a j with hu
  have hu_orb : u ∈ orbA b X j :=
    (orbA b X j).mul_mem ((orbA b X j).inv_mem (hc j hj)) (ha j hj)
  have hY : ∀ Y' ∈ 𝓛, ∀ y ∈ Y', y * u = u * y := by
    intro Y' hY' y hy
    by_cases hYj : Y' = orbA b X j
    · subst hYj
      have hyL : y ∈ L := by
        rw [hL]
        exact (le_sSup hY') hy
      have hyA : y ∈ orbA b X j := hy
      have hcomm' : Commute y (wc * z * wa⁻¹) :=
        ((((hwc' y hyA).symm).mul_right (hzc y ((hAL j hj) hyA))).mul_right
          ((hwa' y hyA).symm.inv_right))
      rw [key]
      exact hcomm'.eq
    · exact (h𝓛 (orbA b X j) (hmem j hj) Y' hY' (fun h' => hYj h'.symm) u hu_orb y hy).symm
  have hcen : L ≤ Subgroup.centralizer ({u} : Set Y) := by
    rw [hL]
    refine sSup_le fun Y' hY' => fun y hy => ?_
    exact Subgroup.mem_centralizer_singleton_iff.2 (hY Y' hY' y hy)
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · exact L.mul_mem (L.inv_mem (hAL j hj (hc j hj))) (hAL j hj (ha j hj))
  · exact Subgroup.mem_centralizer_iff.2 fun l hl =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hcen hl))

theorem conj_mem_center_of_normalizer {L : Subgroup Y} {b u : Y}
    (hbL : b ∈ Subgroup.normalizer (L : Set Y)) (hu : u ∈ L ⊓ Subgroup.centralizer (L : Set Y)) :
    b * u * b⁻¹ ∈ L ⊓ Subgroup.centralizer (L : Set Y) := by
  have hbL' : b⁻¹ ∈ Subgroup.normalizer (L : Set Y) := (Subgroup.normalizer _).inv_mem hbL
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.1 hbL u).1 (Subgroup.mem_inf.1 hu).1
  · refine Subgroup.mem_centralizer_iff.2 fun l hl => ?_
    have hl' : b⁻¹ * l * b⁻¹⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hbL' l).1 hl
    have hc := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hu).2) _ hl'
    have e : l = b * (b⁻¹ * l * b⁻¹⁻¹) * b⁻¹ := by group
    rw [e]
    calc b * (b⁻¹ * l * b⁻¹⁻¹) * b⁻¹ * (b * u * b⁻¹)
        = b * ((b⁻¹ * l * b⁻¹⁻¹) * u) * b⁻¹ := by group
      _ = b * (u * (b⁻¹ * l * b⁻¹⁻¹)) * b⁻¹ := by rw [hc]
      _ = b * u * b⁻¹ * (b * (b⁻¹ * l * b⁻¹⁻¹) * b⁻¹) := by group

theorem orbit_fixed {L : Subgroup Y} {𝓛 : Set (Subgroup Y)} {b : Y} {X : Subgroup Y} {p : ℕ}
    (hp : 0 < p) (hb : orderOf b = p) (hL : L = sSup 𝓛)
    (h𝓛 : ∀ X₁ ∈ 𝓛, ∀ X₂ ∈ 𝓛, X₁ ≠ X₂ → ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x)
    (hmem : ∀ j < p, orbA b X j ∈ 𝓛) (hAL : ∀ j < p, orbA b X j ≤ L)
    (hAcomm : ∀ j k, j < p → k < p → j ≠ k → ∀ x ∈ orbA b X j, ∀ y ∈ orbA b X k, x * y = y * x)
    (hbL : b ∈ Subgroup.normalizer (L : Set Y))
    {g : Y} (hg : g ∈ ⨆ i : Fin p, orbA b X (i : ℕ))
    {z : Y} (hz : z ∈ L ⊓ Subgroup.centralizer (L : Set Y))
    (hfix : b * g * b⁻¹ = g * z) :
    ∃ x ∈ X, ∃ w ∈ L ⊓ Subgroup.centralizer (L : Set Y),
      g = oprod p (fun j => b ^ j * x * (b ^ j)⁻¹) * w := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  have hbp : b ^ (m + 1) = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  obtain ⟨a, ha, hga⟩ := orbit_factor hAcomm hg
  set ã : ℕ → Y := fun j => a (j % (m + 1)) with hã_def
  have hãmem : ∀ j, ã j ∈ orbA b X j := by
    intro j
    have h1 := ha (j % (m + 1)) (Nat.mod_lt _ (Nat.succ_pos m))
    rw [← orbA_mod hb j]
    exact h1
  have hãper : ∀ k, ã (k + (m + 1)) = ã k := by
    intro k
    simp only [hã_def, Nat.add_mod_right]
  have hãlt : ∀ j < m + 1, ã j = a j := by
    intro j hj
    simp only [hã_def, Nat.mod_eq_of_lt hj]
  set F : ℕ → Y := fun j => b * ã j * b⁻¹ with hF_def
  have hFper : ∀ k, F (k + (m + 1)) = F k := by
    intro k
    simp only [hF_def, hãper]
  have hFcomm : ∀ j k, j < m + 1 → k < m + 1 → j ≠ k → Commute (F j) (F k) := by
    intro j k hj hk hjk
    show F j * F k = F k * F j
    have hc := hAcomm j k hj hk hjk (ã j) (hãmem j) (ã k) (hãmem k)
    calc F j * F k = b * (ã j * ã k) * b⁻¹ := by simp only [hF_def]; group
      _ = b * (ã k * ã j) * b⁻¹ := by rw [hc]
      _ = F k * F j := by simp only [hF_def]; group
  have hg_eq : g = oprod (m + 1) ã := by
    rw [hga]
    exact oprod_congr fun j hj => (hãlt j hj).symm
  have hbg : b * g * b⁻¹ = oprod (m + 1) F := by
    rw [hg_eq, conj_oprod]
  have hc_rot : oprod (m + 1) (fun j => F (j + m)) = oprod (m + 1) F :=
    oprod_rot m F hFper hFcomm
  have hc_mem : ∀ j < m + 1, F (j + m) ∈ orbA b X j := by
    intro j hj
    have h2 := conj_mem_orbA_succ (hãmem (j + m))
    have h3 : orbA b X (j + m + 1) = orbA b X j := by
      rw [show j + m + 1 = j + (m + 1) by ring]
      exact orbA_add_period hbp j
    rw [h3] at h2
    exact h2
  have hgz : oprod (m + 1) (fun j => F (j + m)) = oprod (m + 1) ã * z := by
    rw [hc_rot, ← hbg, hfix, hg_eq]
  have hu := block_uniq (a := ã) (c := fun j => F (j + m)) hL h𝓛 hmem hAL hAcomm
    (fun j _ => hãmem j) (fun j hj => hc_mem j hj)
    (Subgroup.inv_mem _ hz) (by
      rw [hgz, mul_inv_cancel_right])
  have hx_mem : ã 0 ∈ X := by
    have h0 := hãmem 0
    rw [orbA_zero] at h0
    exact h0
  set x := ã 0 with hx
  have hrec : ∀ j, j < m + 1 → ∃ u ∈ L ⊓ Subgroup.centralizer (L : Set Y),
      ã j = b ^ j * x * (b ^ j)⁻¹ * u := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨1, (L ⊓ Subgroup.centralizer (L : Set Y)).one_mem, by simp [hx]⟩
    | succ j ih =>
      intro hj1
      obtain ⟨u, hu_mem, hu_eq⟩ := ih (by omega)
      have hcj := hu (j + 1) hj1
      have hFj : F (j + 1 + m) = b * ã j * b⁻¹ := by
        rw [show j + 1 + m = j + (m + 1) by ring]
        exact hFper j
      have hconj : b * ã j * b⁻¹ = b ^ (j + 1) * x * (b ^ (j + 1))⁻¹ * (b * u * b⁻¹) := by
        rw [hu_eq, pow_succ', mul_inv_rev]
        group
      refine ⟨(b * u * b⁻¹) * ((F (j + 1 + m))⁻¹ * ã (j + 1)), ?_, ?_⟩
      · exact (L ⊓ Subgroup.centralizer (L : Set Y)).mul_mem
          (conj_mem_center_of_normalizer hbL hu_mem) hcj
      · have hval : ã (j + 1) = F (j + 1 + m) * ((F (j + 1 + m))⁻¹ * ã (j + 1)) := by group
        rw [hval, hFj, hconj]
        group
  have key' : ∀ j : ℕ, ∃ u : Y, u ∈ L ⊓ Subgroup.centralizer (L : Set Y) ∧
      (j < m + 1 → ã j = b ^ j * x * (b ^ j)⁻¹ * u) := by
    intro j
    by_cases hj : j < m + 1
    · obtain ⟨u, hu', e⟩ := hrec j hj
      exact ⟨u, hu', fun _ => e⟩
    · exact ⟨1, (L ⊓ Subgroup.centralizer (L : Set Y)).one_mem, fun h => absurd h hj⟩
  choose U hU hUeq using key'
  refine ⟨x, hx_mem, oprod (m + 1) U, oprod_mem fun k _ => hU k, ?_⟩
  have hcomm : ∀ j k, j < m + 1 → k < m + 1 → j ≠ k →
      Commute (b ^ j * x * (b ^ j)⁻¹) (U k) := by
    intro j k hj _ _
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hU k)).2)
      _ (hAL j hj (mem_orbA hx_mem))
  have hsplit := oprod_mul_of_comm (n := m + 1) (f := fun j => b ^ j * x * (b ^ j)⁻¹)
    (g := U) hcomm
  have hcomm_eq : oprod (m + 1) ã = oprod (m + 1) (fun j => (b ^ j * x * (b ^ j)⁻¹) * U j) :=
    oprod_congr fun j hj => hUeq j hj
  rw [hg_eq, hcomm_eq]
  exact hsplit

end Orbit

section Components

variable {Y : Type} [Group Y] [Finite Y]

theorem comp_le_or_comm {B H N : Subgroup Y} (hB : CFSG.Assembly.IsComponentOf B H)
    (hNH : N ≤ H) (hN : H ≤ Subgroup.normalizer (N : Set Y)) :
    B ≤ N ∨ ⁅B, N⁆ = ⊥ := by
  have hBH := hB.1
  have hc := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hBH).1 hB
  have hNn : (N.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).2 hN
  rcases CFSG.LocalCores.component_normal_subgroup hc hNn with h | h
  · left
    intro x hx
    have := h (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hBH hx⟩ : H) ∈ B.subgroupOf H)
    exact Subgroup.mem_subgroupOf.mp this
  · right
    have := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hBH h
    rwa [inf_eq_left.2 hNH] at this


theorem exists_noncomm_of_isComponentOf {L R : Subgroup Y} (hR : IsComponentOf R L) :
    ∃ r ∈ R, ∃ t ∈ R, r * t ≠ t * r := by
  by_contra hc
  push_neg at hc
  have hcomm : (⊤ : Subgroup R) ≤ Subgroup.centralizer (⊤ : Subgroup R) := by
    intro a _
    refine Subgroup.mem_centralizer_iff.2 fun b _ => ?_
    exact Subtype.ext (hc b.1 b.2 a.1 a.2)
  have hbot : ⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcomm
  have hq := hR.2.2
  have htriv : (⊤ : Subgroup R) = ⊥ := hq.1.symm.trans hbot
  haveI : Subsingleton R := ⟨fun a b => by
    have ha : a ∈ (⊤ : Subgroup R) := Subgroup.mem_top a
    have hb : b ∈ (⊤ : Subgroup R) := Subgroup.mem_top b
    rw [htriv, Subgroup.mem_bot] at ha hb
    rw [ha, hb]⟩
  haveI := hq.2.toNontrivial
  obtain ⟨u, v, huv⟩ := exists_pair_ne (R ⧸ Subgroup.center R)
  exact huv (Subsingleton.elim _ _)

theorem comp_mem_family {L : Subgroup Y} {𝓛 : Set (Subgroup Y)} (hL : L = sSup 𝓛)
    (hcomp : ∀ X ∈ 𝓛, IsComponentOf X L)
    (hcomm : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x)
    {R : Subgroup Y} (hR : IsComponentOf R L) : R ∈ 𝓛 := by
  by_contra hR𝓛
  have hLN : ∀ X ∈ 𝓛, L ≤ Subgroup.normalizer (X : Set Y) := by
    intro X hX
    rw [hL]
    refine sSup_le fun Y' hY' => fun y hy => ?_
    by_cases hYX : Y' = X
    · subst hYX
      exact Subgroup.le_normalizer hy
    · have hc : ∀ x ∈ X, y * x = x * y := fun x hx => hcomm Y' hY' X hX hYX y hy x hx
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have e : y * h * y⁻¹ = h := by
          rw [hc h hh, mul_assoc, mul_inv_cancel, mul_one]
        rw [e]
        exact hh
      · intro hh
        have hcx : y * (y * h * y⁻¹) = (y * h * y⁻¹) * y := hc _ hh
        have key : y⁻¹ * (y * h * y⁻¹) * y = y * h * y⁻¹ := by
          rw [mul_assoc, ← hcx, ← mul_assoc, inv_mul_cancel, one_mul]
        have e : h = y⁻¹ * (y * h * y⁻¹) * y := by group
        rw [e, key]
        exact hh
  have hRc : ∀ X ∈ 𝓛, R ≤ X ∨ ⁅R, X⁆ = ⊥ := fun X hX =>
    comp_le_or_comm (B := R) (H := L) (N := X) (CFSG.Assembly.isComponentOf_iff_open.2 hR)
      (hcomp X hX).1 (hLN X hX)
  by_cases hsub : ∃ X ∈ 𝓛, R ≤ X
  · obtain ⟨X, hX, hRX⟩ := hsub
    have hsnRX : IsSubnormal R X := isSubnormal_of_le_of_le hR.2.1 hRX (hcomp X hX).1
    rcases CFSG.HardMathSupport.Solomon.Coordinator.i183v_eq_or_le_center hsnRX
        (hcomp X hX).2.2 with heq | hcen
    · exact hR𝓛 (heq ▸ hX)
    · obtain ⟨r, hr, t, ht, hrt⟩ := exists_noncomm_of_isComponentOf hR
      apply hrt
      obtain ⟨z, hz, hzr⟩ := Subgroup.mem_map.1 (hcen hr)
      have hct := Subgroup.mem_center_iff.1 hz ⟨t, hRX ht⟩
      have hct' := congrArg Subtype.val hct
      simp only [Subgroup.coe_mul, Subtype.coe_mk] at hct'
      have hzr' : (z : Y) = r := hzr
      rw [hzr'] at hct'
      exact hct'.symm
  · push_neg at hsub
    have hcentL : ∀ r ∈ R, L ≤ Subgroup.centralizer ({r} : Set Y) := by
      intro r hr
      rw [hL]
      refine sSup_le fun X hX => fun x hx => ?_
      have hRX : ⁅R, X⁆ = ⊥ := (hRc X hX).resolve_left (hsub X hX)
      have hrX : r ∈ Subgroup.centralizer (X : Set Y) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hRX) hr
      exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hrX x hx)
    obtain ⟨r, hr, t, ht, hrt⟩ := exists_noncomm_of_isComponentOf hR
    exact hrt (Subgroup.mem_centralizer_singleton_iff.1 (hcentL r hr (hR.1 ht))).symm


theorem comp_gLBConj_norm {L K : Subgroup Y} {b : Y}
    (hb : b ∈ Subgroup.normalizer (L : Set Y)) (hK : IsComponentOf K L) :
    IsComponentOf (GLBConj b K) L := by
  have hbL : ∀ h, h ∈ L ↔ b * h * b⁻¹ ∈ L := fun h => (Subgroup.mem_normalizer_iff.1 hb h)
  set φ : Y →* Y := (MulAut.conj b⁻¹).toMonoidHom with hφ
  have hφapp : ∀ y, φ y = b⁻¹ * y * b := fun y => by simp [hφ]
  have hLφ : L.map φ = L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hφapp]
      refine (hbL _).2 ?_
      have e : b * (b⁻¹ * y * b) * b⁻¹ = y := by group
      rw [e]
      exact hy
    · intro hx
      refine ⟨b * x * b⁻¹, (hbL x).1 hx, ?_⟩
      rw [hφapp]
      group
  have hK' : IsComponentOf (K.map φ) (L.map φ) :=
    ⟨Subgroup.map_mono hK.1, CFSG.ComponentClassification.Components.chain_map φ hK.2.1,
      CFSG.ComponentClassification.Components.quasisimple_of_equiv
        (K.equivMapOfInjective φ (MulAut.conj b⁻¹).injective).symm hK.2.2⟩
  rw [hLφ] at hK'
  exact hK'

theorem sigma_mem_family {L : Subgroup Y} {𝓛 : Set (Subgroup Y)} (hL : L = sSup 𝓛)
    (hcomp : ∀ X ∈ 𝓛, IsComponentOf X L)
    (hcomm : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x)
    {b : Y} (hbN : b ∈ Subgroup.normalizer (L : Set Y)) {X : Subgroup Y} (hX : X ∈ 𝓛) :
    GLBConj b⁻¹ X ∈ 𝓛 :=
  comp_mem_family hL hcomp hcomm
    (comp_gLBConj_norm ((Subgroup.normalizer _).inv_mem hbN) (hcomp X hX))

theorem orbA_mem_family {L : Subgroup Y} {𝓛 : Set (Subgroup Y)} (hL : L = sSup 𝓛)
    (hcomp : ∀ X ∈ 𝓛, IsComponentOf X L)
    (hcomm : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x)
    {b : Y} (hbN : b ∈ Subgroup.normalizer (L : Set Y)) {X : Subgroup Y} (hX : X ∈ 𝓛)
    (j : ℕ) : orbA b X j ∈ 𝓛 := by
  induction j with
  | zero => rw [orbA_zero]; exact hX
  | succ j ih => rw [orbA_succ]; exact sigma_mem_family hL hcomp hcomm hbN ih


section Gen

variable {Y : Type} [Group Y]

theorem orbA_orbA (b : Y) (X : Subgroup Y) (i j : ℕ) :
    orbA b (orbA b X i) j = orbA b X (i + j) := by
  have e : (b ^ i)⁻¹ * (b ^ j)⁻¹ = (b ^ (i + j))⁻¹ := by
    rw [← mul_inv_rev, ← pow_add, add_comm j i]
  unfold orbA
  rw [gLBConj_gLBConj, e]

def OJ (b : Y) (X : Subgroup Y) : Subgroup Y := ⨆ j : ℕ, orbA b X j

theorem orbA_le_OJ (b : Y) (X : Subgroup Y) (j : ℕ) : orbA b X j ≤ OJ b X :=
  le_iSup (fun j => orbA b X j) j

theorem orbA_add_mul_period {b : Y} {X : Subgroup Y} {p : ℕ} (hbp : b ^ p = 1) (i k : ℕ) :
    orbA b X (k + p * i) = orbA b X k := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [show k + p * (i + 1) = (k + p * i) + p by ring, orbA_add_period hbp, ih]

theorem OJ_orbA_eq {b : Y} {X : Subgroup Y} {p : ℕ} (hbp : b ^ p = 1) (hp : 0 < p) (i : ℕ) :
    OJ b (orbA b X i) = OJ b X := by
  apply le_antisymm
  · refine iSup_le fun j => ?_
    rw [orbA_orbA]
    exact orbA_le_OJ b X (i + j)
  · refine iSup_le fun k => ?_
    have h : orbA b X k = orbA b (orbA b X i) (k + (p - 1) * i) := by
      rw [orbA_orbA]
      have hp' : p = (p - 1) + 1 := by omega
      rw [show i + (k + (p - 1) * i) = k + p * i by
        calc i + (k + (p - 1) * i) = k + ((p - 1) + 1) * i := by ring
          _ = k + p * i := by rw [← hp']]
      exact (orbA_add_mul_period hbp i k).symm
    rw [h]
    exact orbA_le_OJ _ _ _

theorem mem_sup_of_commute {A B : Subgroup Y} (h : ∀ a ∈ A, ∀ c ∈ B, a * c = c * a) {g : Y}
    (hg : g ∈ A ⊔ B) : ∃ a ∈ A, ∃ c ∈ B, g = a * c := by
  let P : Subgroup Y :=
    { carrier := {g | ∃ a ∈ A, ∃ c ∈ B, g = a * c}
      mul_mem' := by
        rintro _ _ ⟨a, ha, c, hc, rfl⟩ ⟨a', ha', c', hc', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', c * c', B.mul_mem hc hc', ?_⟩
        calc a * c * (a' * c') = a * (c * a') * c' := by group
          _ = a * (a' * c) * c' := by rw [← h a' ha' c hc]
          _ = a * a' * (c * c') := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, c, hc, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, c⁻¹, B.inv_mem hc, ?_⟩
        have e : c⁻¹ * a⁻¹ = a⁻¹ * c⁻¹ := by
          rw [← mul_inv_rev, ← mul_inv_rev, h a ha c hc]
        rw [mul_inv_rev, e] }
  have hAP : A ≤ P := fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩
  have hBP : B ≤ P := fun c hc => ⟨1, A.one_mem, c, hc, by simp⟩
  obtain ⟨a, ha, c, hc, rfl⟩ := (sup_le hAP hBP : A ⊔ B ≤ P) hg
  exact ⟨a, ha, c, hc, rfl⟩

theorem commute_iSup {ι κ : Type} (S : ι → Subgroup Y) (T : κ → Subgroup Y)
    (h : ∀ i k, ∀ x ∈ S i, ∀ y ∈ T k, x * y = y * x) {x y : Y}
    (hx : x ∈ ⨆ i, S i) (hy : y ∈ ⨆ k, T k) : x * y = y * x := by
  refine Subgroup.iSup_induction S (C := fun x => x * y = y * x) hx (fun i x hx' => ?_) ?_
    (fun a b ha hb => ?_)
  · refine Subgroup.iSup_induction T (C := fun y => x * y = y * x) hy
      (fun k y hy' => h i k x hx' y hy') ?_ (fun c d hc hd => ?_)
    · simp
    · rw [← mul_assoc, hc, mul_assoc, hd, ← mul_assoc]
  · simp
  · rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]


theorem OJ_comm_of_ne {𝓛 : Set (Subgroup Y)} {b : Y} {p : ℕ} (hbp : b ^ p = 1)
    (hp : 0 < p)
    (hmem : ∀ X ∈ 𝓛, ∀ j : ℕ, orbA b X j ∈ 𝓛)
    (h𝓛 : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x)
    {X X' : Subgroup Y} (hX : X ∈ 𝓛) (hX' : X' ∈ 𝓛) (hne : OJ b X ≠ OJ b X') :
    ∀ x ∈ OJ b X, ∀ y ∈ OJ b X', x * y = y * x := by
  intro x hx y hy
  refine commute_iSup (fun j => orbA b X j) (fun k => orbA b X' k) (fun j k u hu v hv => ?_) hx hy
  have hne' : orbA b X j ≠ orbA b X' k := by
    intro heq
    apply hne
    calc OJ b X = OJ b (orbA b X j) := (OJ_orbA_eq (X := X) hbp hp j).symm
      _ = OJ b (orbA b X' k) := by rw [heq]
      _ = OJ b X' := OJ_orbA_eq (X := X') hbp hp k
  exact h𝓛 _ (hmem X hX j) _ (hmem X' hX' k) hne' u hu v hv

theorem conj_mem_OJ {b : Y} (X : Subgroup Y) {y : Y} (hy : y ∈ OJ b X) :
    b * y * b⁻¹ ∈ OJ b X := by
  refine Subgroup.iSup_induction (fun j => orbA b X j) (C := fun y => b * y * b⁻¹ ∈ OJ b X)
    hy (fun j y hy' => orbA_le_OJ b X (j + 1) (conj_mem_orbA_succ hy')) ?_
    (fun u v hu hv => ?_)
  · simp only [mul_inv_cancel, mul_one]
    exact (OJ b X).one_mem
  · have e : b * (u * v) * b⁻¹ = (b * u * b⁻¹) * (b * v * b⁻¹) := by group
    rw [e]
    exact (OJ b X).mul_mem hu hv

theorem conj_mem_sSup {b : Y} {𝔉 : Set (Subgroup Y)} (hinv : ∀ O ∈ 𝔉, ∀ y ∈ O, b * y * b⁻¹ ∈ O)
    {y : Y} (hy : y ∈ sSup 𝔉) : b * y * b⁻¹ ∈ sSup 𝔉 := by
  rw [sSup_eq_iSup'] at hy ⊢
  refine Subgroup.iSup_induction (fun O : 𝔉 => O.1) (C := fun y => b * y * b⁻¹ ∈ ⨆ O : 𝔉, O.1)
    hy (fun O y hy' => le_iSup (fun O : 𝔉 => O.1) O (hinv O.1 O.2 y hy')) ?_ (fun u v hu hv => ?_)
  · simp only [mul_inv_cancel, mul_one]
    exact (⨆ O : 𝔉, O.1).one_mem
  · have e : b * (u * v) * b⁻¹ = (b * u * b⁻¹) * (b * v * b⁻¹) := by group
    rw [e]
    exact (⨆ O : 𝔉, O.1).mul_mem hu hv

theorem block2 {L O F : Subgroup Y} {𝓛 : Set (Subgroup Y)} (hL : L = sSup 𝓛)
    (hO : O ≤ L) (hF : F ≤ L)
    (hOF : ∀ o ∈ O, ∀ f ∈ F, o * f = f * o)
    (hOc : ∀ X ∈ 𝓛, X ≤ O ∨ ∀ x ∈ X, ∀ o ∈ O, x * o = o * x)
    {o a1 f a2 z : Y} (ho : o ∈ O) (ha1 : a1 ∈ O) (hf : f ∈ F) (ha2 : a2 ∈ F)
    (hz : z ∈ L ⊓ Subgroup.centralizer (L : Set Y)) (h : a1 * a2 = o * f * z) :
    o⁻¹ * a1 ∈ L ⊓ Subgroup.centralizer (L : Set Y) ∧
      f⁻¹ * a2 ∈ L ⊓ Subgroup.centralizer (L : Set Y) := by
  have ha1' : a1 = o * f * z * a2⁻¹ := by rw [← h]; group
  set u := o⁻¹ * a1 with hu
  have hu_eq : u = f * z * a2⁻¹ := by rw [hu, ha1']; group
  have hu_comm : ∀ o' ∈ O, o' * u = u * o' := by
    intro o' ho'
    have c1 : Commute o' f := hOF o' ho' f hf
    have c2 : Commute o' z := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2) o' (hO ho')
    have c3 : Commute o' a2 := hOF o' ho' a2 ha2
    have c4 : Commute o' (f * z * a2⁻¹) := (c1.mul_right c2).mul_right c3.inv_right
    rw [hu_eq]
    exact c4.eq
  have huL : u ∈ L := L.mul_mem (L.inv_mem (hO ho)) (hO ha1)
  have hcen : L ≤ Subgroup.centralizer ({u} : Set Y) := by
    rw [hL]
    refine sSup_le fun X hX => fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hOc X hX with hXO | hXc
    · exact hu_comm x (hXO hx)
    · exact hXc x hx u (O.mul_mem (O.inv_mem ho) ha1)
  have hu_cen : u ∈ Subgroup.centralizer (L : Set Y) :=
    Subgroup.mem_centralizer_iff.2 fun l hl => Subgroup.mem_centralizer_singleton_iff.1 (hcen hl)
  have hu_Z : u ∈ L ⊓ Subgroup.centralizer (L : Set Y) := Subgroup.mem_inf.2 ⟨huL, hu_cen⟩
  have hua : u * a2 = f * z := by
    have h1 : o * (u * a2) = o * (f * z) := by
      have hou : o * u = a1 := by rw [hu]; group
      calc o * (u * a2) = o * u * a2 := by group
        _ = a1 * a2 := by rw [hou]
        _ = o * f * z := h
        _ = o * (f * z) := by group
    exact mul_left_cancel h1
  have hcf : Commute f u := (Subgroup.mem_centralizer_iff.1 hu_cen) f (hF hf)
  have hfa : f⁻¹ * a2 = u⁻¹ * z := by
    have ha2' : a2 = u⁻¹ * (f * z) := by rw [← hua]; group
    rw [ha2']
    have hc' : Commute f u⁻¹ := hcf.inv_right
    calc f⁻¹ * (u⁻¹ * (f * z)) = (f⁻¹ * u⁻¹ * f) * z := by group
      _ = u⁻¹ * z := by
        congr 1
        calc f⁻¹ * u⁻¹ * f = f⁻¹ * (u⁻¹ * f) := by group
          _ = f⁻¹ * (f * u⁻¹) := by rw [← hc'.eq]
          _ = u⁻¹ := by group
  refine ⟨hu_Z, ?_⟩
  rw [hfa]
  exact (L ⊓ Subgroup.centralizer (L : Set Y)).mul_mem
    ((L ⊓ Subgroup.centralizer (L : Set Y)).inv_mem hu_Z) hz


theorem gen_fin {L : Subgroup Y} {𝓛 : Set (Subgroup Y)} {b : Y} {p : ℕ}
    (hbp : b ^ p = 1) (hp : 0 < p) (hL : L = sSup 𝓛)
    (hmem : ∀ X ∈ 𝓛, ∀ j : ℕ, orbA b X j ∈ 𝓛)
    (h𝓛 : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x)
    (D : Subgroup Y → Subgroup Y)
    (hSO : ∀ X ∈ 𝓛, ∀ o ∈ OJ b X, ∀ z ∈ L ⊓ Subgroup.centralizer (L : Set Y),
      b * o * b⁻¹ = o * z → o ∈ D X ⊔ (L ⊓ Subgroup.centralizer (L : Set Y)))
    (𝔉 : Set (Subgroup Y)) (hfin : 𝔉.Finite) :
    (∀ O ∈ 𝔉, ∃ X ∈ 𝓛, OJ b X = O) → ∀ g ∈ sSup 𝔉,
      (∃ z ∈ L ⊓ Subgroup.centralizer (L : Set Y), b * g * b⁻¹ = g * z) →
      g ∈ (⨆ X ∈ {X | X ∈ 𝓛 ∧ OJ b X ∈ 𝔉}, D X) ⊔ (L ⊓ Subgroup.centralizer (L : Set Y)) := by
  induction 𝔉, hfin using Set.Finite.induction_on with
  | empty =>
    intro _ g hg _
    rw [sSup_empty, Subgroup.mem_bot] at hg
    rw [hg]
    exact Subgroup.one_mem _
  | insert ha hs ih =>
    rename_i a s
    intro hyp g hg hfix
    obtain ⟨X₀, hX₀, hOX₀⟩ := hyp a (Set.mem_insert a s)
    have hyp' : ∀ O ∈ s, ∃ X ∈ 𝓛, OJ b X = O := fun O hO => hyp O (Set.mem_insert_of_mem a hO)
    have hOL : ∀ X ∈ 𝓛, OJ b X ≤ L := fun X hX => by
      rw [hL]
      exact iSup_le fun j => le_sSup (hmem X hX j)
    have hinv_s : ∀ O ∈ s, ∀ y ∈ O, b * y * b⁻¹ ∈ O := by
      intro O hO y hy
      obtain ⟨X', hX', hOX'⟩ := hyp' O hO
      rw [← hOX'] at hy ⊢
      exact conj_mem_OJ X' hy
    have hcomm_as : ∀ o ∈ a, ∀ f ∈ sSup s, o * f = f * o := by
      intro o ho f hf
      rw [sSup_eq_iSup'] at hf
      have ho' : o ∈ ⨆ _ : Unit, a := by rw [iSup_const]; exact ho
      refine commute_iSup (fun _ : Unit => a) (fun O : s => (O : Subgroup Y))
        (fun _ k x hx y hy => ?_) ho' hf
      obtain ⟨X', hX', hOX'⟩ := hyp' k.1 k.2
      have hne : OJ b X₀ ≠ OJ b X' := by
        rw [hOX₀, hOX']
        intro heq
        exact ha (heq ▸ k.2)
      rw [← hOX₀] at hx
      rw [← hOX'] at hy
      exact OJ_comm_of_ne hbp hp hmem h𝓛 hX₀ hX' hne x hx y hy
    rw [sSup_insert] at hg
    obtain ⟨o, ho, f, hf, rfl⟩ := mem_sup_of_commute hcomm_as hg
    obtain ⟨z, hz, hfix'⟩ := hfix
    have ho' : o ∈ OJ b X₀ := by rw [hOX₀]; exact ho
    have hbo : b * o * b⁻¹ ∈ a := by
      rw [← hOX₀]
      exact conj_mem_OJ X₀ ho'
    have hbf : b * f * b⁻¹ ∈ sSup s := conj_mem_sSup hinv_s hf
    have hsplit : (b * o * b⁻¹) * (b * f * b⁻¹) = o * f * z := by
      calc (b * o * b⁻¹) * (b * f * b⁻¹) = b * (o * f) * b⁻¹ := by group
        _ = o * f * z := hfix'
    have haL : a ≤ L := by rw [← hOX₀]; exact hOL X₀ hX₀
    have hsL : sSup s ≤ L := sSup_le fun O hO => by
      obtain ⟨X', hX', hOX'⟩ := hyp' O hO
      rw [← hOX']
      exact hOL X' hX'
    have hOc : ∀ X ∈ 𝓛, X ≤ a ∨ ∀ x ∈ X, ∀ o' ∈ a, x * o' = o' * x := by
      intro X hX
      by_cases hXa : OJ b X = a
      · left
        rw [← hXa]
        have := orbA_le_OJ b X 0
        rwa [orbA_zero] at this
      · right
        intro x hx o' ho''
        have hne : OJ b X ≠ OJ b X₀ := by rw [hOX₀]; exact hXa
        have hxO : x ∈ OJ b X := orbA_le_OJ b X 0 (by rw [orbA_zero]; exact hx)
        have ho3 : o' ∈ OJ b X₀ := by rw [hOX₀]; exact ho''
        exact OJ_comm_of_ne hbp hp hmem h𝓛 hX hX₀ hne x hxO o' ho3
    obtain ⟨hz1, hz2⟩ := block2 hL haL hsL hcomm_as hOc ho hbo hf hbf hz hsplit
    have hoS := hSO X₀ hX₀ o ho' (o⁻¹ * (b * o * b⁻¹)) hz1 (by group)
    have hfIH := ih hyp' f hf ⟨f⁻¹ * (b * f * b⁻¹), hz2, by group⟩
    have hD0 : D X₀ ≤ ⨆ X ∈ {X | X ∈ 𝓛 ∧ OJ b X ∈ insert a s}, D X :=
      le_iSup₂_of_le X₀ (show X₀ ∈ 𝓛 ∧ OJ b X₀ ∈ insert a s from
        ⟨hX₀, by rw [hOX₀]; exact Set.mem_insert a s⟩) le_rfl
    have hT_mono : (⨆ X ∈ {X | X ∈ 𝓛 ∧ OJ b X ∈ s}, D X) ≤
        ⨆ X ∈ {X | X ∈ 𝓛 ∧ OJ b X ∈ insert a s}, D X :=
      iSup₂_le fun X hX => le_iSup₂_of_le X
        (show X ∈ 𝓛 ∧ OJ b X ∈ insert a s from ⟨hX.1, Set.mem_insert_of_mem a hX.2⟩) le_rfl
    have hoT : o ∈ (⨆ X ∈ {X | X ∈ 𝓛 ∧ OJ b X ∈ insert a s}, D X) ⊔
        (L ⊓ Subgroup.centralizer (L : Set Y)) :=
      (sup_le_sup hD0 le_rfl : D X₀ ⊔ (L ⊓ Subgroup.centralizer (L : Set Y)) ≤ _) hoS
    have hfT : f ∈ (⨆ X ∈ {X | X ∈ 𝓛 ∧ OJ b X ∈ insert a s}, D X) ⊔
        (L ⊓ Subgroup.centralizer (L : Set Y)) :=
      (sup_le_sup hT_mono le_rfl : (⨆ X ∈ {X | X ∈ 𝓛 ∧ OJ b X ∈ s}, D X) ⊔
        (L ⊓ Subgroup.centralizer (L : Set Y)) ≤ _) hfIH
    exact Subgroup.mul_mem _ hoT hfT

theorem normalizer_of_commute {S : Subgroup Y} {g : Y} (h : ∀ s ∈ S, g * s = s * g) :
    g ∈ Subgroup.normalizer (S : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have e : g * x * g⁻¹ = x := by rw [h x hx]; group
    rw [e]
    exact hx
  · intro hx
    have hc : g * (g * x * g⁻¹) = (g * x * g⁻¹) * g := h _ hx
    have hy : g⁻¹ * (g * x * g⁻¹) * g = g * x * g⁻¹ := by
      calc g⁻¹ * (g * x * g⁻¹) * g = g⁻¹ * ((g * x * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * x * g⁻¹)) := by rw [hc]
        _ = g * x * g⁻¹ := by group
    have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [e, hy]
    exact hx

theorem core_gen_normal [Finite Y] {L : Subgroup Y} {𝓛 : Set (Subgroup Y)} {b : Y} {p : ℕ}
    (hbp : b ^ p = 1) (hp : 0 < p) (hL : L = sSup 𝓛)
    (hmem : ∀ X ∈ 𝓛, ∀ j : ℕ, orbA b X j ∈ 𝓛)
    (h𝓛 : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x)
    (D : Subgroup Y → Subgroup Y)
    (hDM : ∀ X ∈ 𝓛, D X ≤ L ⊓ Subgroup.centralizer ({b} : Set Y))
    (hDOJ : ∀ X ∈ 𝓛, D X ≤ OJ b X)
    (hSO : ∀ X ∈ 𝓛, ∀ o ∈ OJ b X, ∀ z ∈ L ⊓ Subgroup.centralizer (L : Set Y),
      b * o * b⁻¹ = o * z → o ∈ D X ⊔ (L ⊓ Subgroup.centralizer (L : Set Y)))
    (hDeq : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, OJ b X = OJ b X' →
      D X' ≤ D X ⊔ (L ⊓ Subgroup.centralizer (L : Set Y))) :
    (∀ m ∈ L ⊓ Subgroup.centralizer ({b} : Set Y), ∃ d ∈ ⨆ X ∈ 𝓛, D X,
      ∃ w ∈ L ⊓ Subgroup.centralizer (L : Set Y), m = d * w) ∧
    (∀ X ∈ 𝓛, ∀ m ∈ L ⊓ Subgroup.centralizer ({b} : Set Y),
      m ∈ Subgroup.normalizer (D X : Set Y)) := by
  classical
  set ZL := L ⊓ Subgroup.centralizer (L : Set Y) with hZL
  set M := L ⊓ Subgroup.centralizer ({b} : Set Y) with hM
  set 𝔉 : Set (Subgroup Y) := (fun X => OJ b X) '' 𝓛 with h𝔉
  have h𝔉fin : 𝔉.Finite := Set.Finite.image _ (Set.toFinite 𝓛)
  have hyp : ∀ O ∈ 𝔉, ∃ X ∈ 𝓛, OJ b X = O := by
    rintro O ⟨X, hX, rfl⟩
    exact ⟨X, hX, rfl⟩
  have hLle : L ≤ sSup 𝔉 := by
    rw [hL]
    refine sSup_le fun X hX => ?_
    exact (orbA_zero b X ▸ orbA_le_OJ b X 0).trans (le_sSup ⟨X, hX, rfl⟩)
  have hgen := gen_fin hbp hp hL hmem h𝓛 D hSO 𝔉 h𝔉fin hyp
  have hset : {X | X ∈ 𝓛 ∧ OJ b X ∈ 𝔉} = 𝓛 := by
    ext X
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h => h.1, fun hX => ⟨hX, X, hX, rfl⟩⟩
  have hDL : ∀ X ∈ 𝓛, D X ≤ L := fun X hX => (hDM X hX).trans inf_le_left
  have hsupL : (⨆ X ∈ 𝓛, D X) ≤ L := iSup₂_le fun X hX => hDL X hX
  have hcommZ : ∀ a ∈ (⨆ X ∈ 𝓛, D X), ∀ c ∈ ZL, a * c = c * a := fun a ha c hc =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2) a (hsupL ha)
  have hC1 : ∀ m ∈ M, ∃ d ∈ ⨆ X ∈ 𝓛, D X, ∃ w ∈ ZL, m = d * w := by
    intro m hm
    have hmL : m ∈ L := (Subgroup.mem_inf.1 hm).1
    have hmC : m ∈ Subgroup.centralizer ({b} : Set Y) := (Subgroup.mem_inf.1 hm).2
    have hfix : ∃ z ∈ ZL, b * m * b⁻¹ = m * z := by
      refine ⟨1, ZL.one_mem, ?_⟩
      rw [mul_one]
      have hbm := Subgroup.mem_centralizer_singleton_iff.1 hmC
      calc b * m * b⁻¹ = m * b * b⁻¹ := by rw [hbm]
        _ = m := by group
    have hT := hgen m (hLle hmL) hfix
    rw [hset] at hT
    obtain ⟨d, hd, w, hw, hdw⟩ := mem_sup_of_commute hcommZ hT
    exact ⟨d, hd, w, hw, hdw⟩
  refine ⟨hC1, fun X hX m hm => ?_⟩
  have hZN : ZL ≤ Subgroup.normalizer (D X : Set Y) := fun z hz =>
    normalizer_of_commute fun s hs =>
      ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2) s (hDL X hX hs)).symm
  have hDN : ∀ Y' ∈ 𝓛, D Y' ≤ Subgroup.normalizer (D X : Set Y) := by
    intro Y' hY' d hd
    by_cases hOJ : OJ b Y' = OJ b X
    · have hd' := hDeq X hX Y' hY' hOJ.symm hd
      refine (sup_le (fun n hn => Subgroup.le_normalizer hn) hZN) hd'
    · refine normalizer_of_commute fun n hn => ?_
      exact OJ_comm_of_ne hbp hp hmem h𝓛 hY' hX hOJ d (hDOJ Y' hY' hd) n (hDOJ X hX hn)
  have hMN : (⨆ Y' ∈ 𝓛, D Y') ≤ Subgroup.normalizer (D X : Set Y) :=
    iSup₂_le fun Y' hY' => hDN Y' hY'
  obtain ⟨d, hd, w, hw, rfl⟩ := hC1 m hm
  exact (Subgroup.normalizer _).mul_mem (hMN hd) (hZN hw)

theorem quot_diag_iso [Finite Y] {p : ℕ} (hp : p.Prime) {M : Subgroup Y}
    {𝓛 : Set (Subgroup Y)}
    (D : Subgroup Y → Subgroup Y)
    (hDM : ∀ X ∈ 𝓛, D X ≤ M)
    (hgen : ∀ m ∈ M, ∃ d ∈ ⨆ X ∈ 𝓛, D X, ∃ w : Y, (∀ n ∈ M, w * n = n * w) ∧ m = d * w)
    (hDN : ∀ X ∈ 𝓛, ∀ m ∈ M, m ∈ Subgroup.normalizer (D X : Set Y))
    (hψ : ∀ X ∈ 𝓛, ∃ ψ : ↥X →* Y, ψ.range = D X)
    (hXq : ∀ X ∈ 𝓛, CFSG.Open.IsQuasisimple ↥X)
    {Q : Subgroup Y} (hQ : GLAPComponent p M Q) :
    ∃ X ∈ 𝓛, Nonempty ((↥Q ⧸ GLAPPrimeCore p ↥Q) ⧸ Subgroup.center (↥Q ⧸ GLAPPrimeCore p ↥Q) ≃*
      (↥X ⧸ Subgroup.center ↥X)) := by
  classical
  obtain ⟨hQM, hsnQ, hcompQ, -⟩ := hQ
  set P := GLAPPrimeCore p ↥M with hP
  set R : Subgroup (↥M ⧸ P) := barX p M Q with hR
  have hRc : IsComponentOf R ⊤ := hcompQ
  set K : Subgroup Y → Subgroup (↥M ⧸ P) := fun X => ((D X).subgroupOf M).map
    (QuotientGroup.mk' P) with hK
  have hKn : ∀ X ∈ 𝓛, (K X).Normal := by
    intro X hX
    have hN : ((D X).subgroupOf M).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hgN := hDN X hX g.1 g.2
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.1 hgN _).1 hn
    exact hN.map (QuotientGroup.mk' P) (QuotientGroup.mk'_surjective P)
  have hdich : ∀ X ∈ 𝓛, R ≤ K X ∨ ⁅R, K X⁆ = ⊥ := fun X hX => by
    haveI := hKn X hX
    exact CFSG.LocalCores.component_normal_subgroup ((CFSG.isComponent_iff_open R).2 hRc)
      inferInstance
  have hcomm_of : ∀ X ∈ 𝓛, (⁅R, K X⁆ = ⊥) → ∀ r ∈ R, ∀ k ∈ K X, k * r = r * k := by
    intro X hX hc r hr k hk
    have h1 : r ∈ Subgroup.centralizer (K X : Set (↥M ⧸ P)) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc) hr
    exact (Subgroup.mem_centralizer_iff.1 h1) k hk
  have hexists : ∃ X ∈ 𝓛, R ≤ K X := by
    by_contra hno
    push_neg at hno
    have hall : ∀ X ∈ 𝓛, ⁅R, K X⁆ = ⊥ := fun X hX => (hdich X hX).resolve_left (hno X hX)
    have hsupc : ∀ y ∈ ⨆ X ∈ 𝓛, D X, ∃ hy : y ∈ M,
        ∀ r ∈ R, QuotientGroup.mk' P ⟨y, hy⟩ * r = r * QuotientGroup.mk' P ⟨y, hy⟩ := by
      intro y hy
      refine Subgroup.iSup_induction (fun X : Subgroup Y => ⨆ (_ : X ∈ 𝓛), D X)
        (C := fun y => ∃ hy : y ∈ M,
          ∀ r ∈ R, QuotientGroup.mk' P ⟨y, hy⟩ * r = r * QuotientGroup.mk' P ⟨y, hy⟩)
        hy ?_ ?_ ?_
      · intro X y hy'
        by_cases hX : X ∈ 𝓛
        · rw [iSup_pos hX] at hy'
          have hyM : y ∈ M := hDM X hX hy'
          refine ⟨hyM, fun r hr => ?_⟩
          have hmem : QuotientGroup.mk' P ⟨y, hyM⟩ ∈ K X :=
            Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hy')
          exact hcomm_of X hX (hall X hX) r hr _ hmem
        · rw [iSup_neg hX, Subgroup.mem_bot] at hy'
          subst hy'
          refine ⟨M.one_mem, fun r hr => ?_⟩
          rw [show QuotientGroup.mk' P (⟨1, M.one_mem⟩ : ↥M) = 1 from map_one _, one_mul, mul_one]
      · refine ⟨M.one_mem, fun r hr => ?_⟩
        rw [show QuotientGroup.mk' P (⟨1, M.one_mem⟩ : ↥M) = 1 from map_one _, one_mul, mul_one]
      · rintro x z ⟨hxM, hx⟩ ⟨hzM, hz⟩
        have hxzM : x * z ∈ M := M.mul_mem hxM hzM
        refine ⟨hxzM, fun r hr => ?_⟩
        have e : QuotientGroup.mk' P ⟨x * z, hxzM⟩ = QuotientGroup.mk' P ⟨x, hxM⟩ *
            QuotientGroup.mk' P ⟨z, hzM⟩ := by
          rw [← map_mul]
          rfl
        rw [e, mul_assoc, hz r hr, ← mul_assoc, hx r hr, mul_assoc]
    have hcen : ∀ r ∈ R, ∀ g : ↥M ⧸ P, g * r = r * g := by
      intro r hr g
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective P g
      obtain ⟨d, hd, w, hw, hmw⟩ := hgen m.1 m.2
      have hdM : d ∈ M := (iSup₂_le fun X hX => hDM X hX) hd
      have hwM : w ∈ M := by
        have e : w = d⁻¹ * m.1 := by rw [hmw]; group
        rw [e]
        exact M.mul_mem (M.inv_mem hdM) m.2
      have e : QuotientGroup.mk' P m = QuotientGroup.mk' P ⟨d, hdM⟩ * QuotientGroup.mk' P ⟨w, hwM⟩ := by
        rw [← map_mul]
        congr 1
        exact Subtype.ext hmw
      have hW : ∀ g' : ↥M ⧸ P, QuotientGroup.mk' P ⟨w, hwM⟩ * g' = g' * QuotientGroup.mk' P ⟨w, hwM⟩ := by
        intro g'
        obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective P g'
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hw n.1 n.2)
      obtain ⟨_, hcd⟩ := hsupc d hd
      rw [e]
      calc QuotientGroup.mk' P ⟨d, hdM⟩ * QuotientGroup.mk' P ⟨w, hwM⟩ * r
          = QuotientGroup.mk' P ⟨d, hdM⟩ * (QuotientGroup.mk' P ⟨w, hwM⟩ * r) := by rw [mul_assoc]
        _ = QuotientGroup.mk' P ⟨d, hdM⟩ * (r * QuotientGroup.mk' P ⟨w, hwM⟩) := by rw [hW r]
        _ = (QuotientGroup.mk' P ⟨d, hdM⟩ * r) * QuotientGroup.mk' P ⟨w, hwM⟩ := by rw [mul_assoc]
        _ = (r * QuotientGroup.mk' P ⟨d, hdM⟩) * QuotientGroup.mk' P ⟨w, hwM⟩ := by rw [hcd r hr]
        _ = r * (QuotientGroup.mk' P ⟨d, hdM⟩ * QuotientGroup.mk' P ⟨w, hwM⟩) := by rw [mul_assoc]
    obtain ⟨r, hr, t, ht, hrt⟩ := exists_noncomm_of_isComponentOf hRc
    exact hrt (hcen r hr t).symm
  obtain ⟨X₀, hX₀, hRK⟩ := hexists
  obtain ⟨ψ, hψr⟩ := hψ X₀ hX₀
  have hψM : ∀ x : ↥X₀, ψ x ∈ M := fun x =>
    hDM X₀ hX₀ (by rw [← hψr]; exact MonoidHom.mem_range.2 ⟨x, rfl⟩)
  set φ : ↥X₀ →* (↥M ⧸ P) := (QuotientGroup.mk' P).comp (ψ.codRestrict M hψM) with hφ
  have hφr : φ.range = K X₀ := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine Subgroup.mem_map.2 ⟨⟨ψ x, hψM x⟩, ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf, ← hψr]
      exact MonoidHom.mem_range.2 ⟨x, rfl⟩
    · intro hz
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hz
      rw [Subgroup.mem_subgroupOf, ← hψr] at hm
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hm
      refine ⟨x, ?_⟩
      apply congrArg (QuotientGroup.mk' P)
      exact Subtype.ext hx
  set T := φ.ker with hT
  have hTn : T.Normal := MonoidHom.normal_ker φ
  have hT_ne : T ≠ ⊤ := by
    intro htop
    have hbot : K X₀ = ⊥ := by
      rw [← hφr, eq_bot_iff]
      rintro _ ⟨x, rfl⟩
      have hx : x ∈ T := by rw [htop]; exact Subgroup.mem_top x
      rw [MonoidHom.mem_ker] at hx
      rw [hx]
      exact Subgroup.one_mem _
    have hR0 : R = ⊥ := le_bot_iff.1 (hbot ▸ hRK)
    obtain ⟨r, hr, t, ht, hrt⟩ := exists_noncomm_of_isComponentOf hRc
    rw [hR0, Subgroup.mem_bot] at hr ht
    exact hrt (by rw [hr, ht])
  have hTc : T ≤ Subgroup.center ↥X₀ := l119_normal_le_center (hXq X₀ hX₀) hT_ne
  set φ' : ↥X₀ →* ↥(K X₀) := φ.codRestrict (K X₀) (fun x => by
    rw [← hφr]
    exact MonoidHom.mem_range.2 ⟨x, rfl⟩) with hφ'
  have hφ'surj : Function.Surjective φ' := by
    rintro ⟨z, hz⟩
    rw [← hφr] at hz
    obtain ⟨x, hx⟩ := hz
    exact ⟨x, Subtype.ext hx⟩
  have hker : φ'.ker = T := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      have := congrArg Subtype.val h
      exact this
    · intro h
      exact Subtype.ext h
  let eK : (↥X₀ ⧸ T) ≃* ↥(K X₀) := (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective φ' hφ'surj)
  have hKq : CFSG.Open.IsQuasisimple ↥(K X₀) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eK
      (CFSG.ComponentClassification.Quasisimple.central_quotient (hXq X₀ hX₀) T hTc)
  have hsnRK : IsSubnormal R (K X₀) := isSubnormal_of_le_of_le hRc.2.1 hRK le_top
  have hRK_eq : R = K X₀ := by
    rcases CFSG.HardMathSupport.Solomon.Coordinator.i183v_eq_or_le_center hsnRK hKq with h | h
    · exact h
    · exfalso
      obtain ⟨r, hr, t, ht, hrt⟩ := exists_noncomm_of_isComponentOf hRc
      apply hrt
      obtain ⟨z, hz, hzr⟩ := Subgroup.mem_map.1 (h hr)
      have htK : t ∈ K X₀ := hRK ht
      have hc := Subgroup.mem_center_iff.1 hz ⟨t, htK⟩
      have hc' := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul, Subtype.coe_mk] at hc'
      have hz' : ((z : ↥(K X₀)) : ↥M ⧸ P) = r := hzr
      rw [hz'] at hc'
      exact hc'.symm
  have e1 : (↥Q ⧸ GLAPPrimeCore p ↥Q) ≃* ↥R := quotEquivBarX hp hQM hsnQ
  have e2 : ↥R ≃* ↥(K X₀) := MulEquiv.subgroupCongr hRK_eq
  have e3 : ↥(K X₀) ≃* ↥X₀ ⧸ T := eK.symm
  haveI := hTn
  obtain ⟨eZ⟩ := l119_center_quot_iso (hXq X₀ hX₀) hTc
  exact ⟨X₀, hX₀, ⟨(l119_centerQuot_equiv (e1.trans (e2.trans e3))).trans eZ⟩⟩

theorem normalizer_of_gLBConj_eq {Y : Type} [Group Y] {X : Subgroup Y} {g : Y}
    (h : GLBConj g X = X) : g ∈ Subgroup.normalizer (X : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hx := @mem_gLBConj Y _ g x X
  rw [h] at hx
  exact hx

end Gen

section Case

variable {Y : Type} [Group Y]

theorem orbA_ne_aux {X : Subgroup Y} {b : Y} {p : ℕ} (hp : p.Prime)
    (hb : orderOf b = p) (hnot : b ∉ Subgroup.normalizer (X : Set Y))
    (j n : ℕ) (hn : 0 < n) (hnp : n < p) : orbA b X j ≠ orbA b X (j + n) := by
  intro heq
  have hbp : b ^ p = 1 := hb ▸ pow_orderOf_eq_one b
  have e1 : GLBConj (b ^ j) (orbA b X j) = X := by
    unfold orbA
    rw [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one]
  have e2 : GLBConj (b ^ j) (orbA b X (j + n)) = GLBConj (b ^ n)⁻¹ X := by
    unfold orbA
    rw [gLBConj_gLBConj, pow_add, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  have hX : GLBConj (b ^ n)⁻¹ X = X := by
    rw [← e2, ← heq, e1]
  have hn' : b ^ n ∈ Subgroup.normalizer (X : Set Y) := by
    have := (Subgroup.normalizer _).inv_mem (normalizer_of_gLBConj_eq hX)
    rwa [inv_inv] at this
  have hcop : IsCoprime (n : ℤ) (p : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 (fun h => by
      have := Nat.le_of_dvd hn h
      omega))
  obtain ⟨u, v, huv⟩ := hcop
  apply hnot
  have hb_eq : b = (b ^ n) ^ u := by
    have e1 : b ^ (u * (n : ℤ)) = (b ^ (n : ℤ)) ^ u := by rw [← zpow_mul, mul_comm]
    have e2 : b ^ (v * (p : ℤ)) = 1 := by
      rw [mul_comm, zpow_mul, zpow_natCast, hbp, one_zpow]
    calc b = b ^ (u * (n : ℤ) + v * (p : ℤ)) := by rw [huv, zpow_one]
      _ = b ^ (u * (n : ℤ)) * b ^ (v * (p : ℤ)) := zpow_add b _ _
      _ = (b ^ n) ^ u := by rw [e1, e2, mul_one, zpow_natCast]
  rw [hb_eq]
  exact (Subgroup.normalizer _).zpow_mem hn' u

theorem orbA_ne_of_not_normalizer {X : Subgroup Y} {b : Y} {p : ℕ} (hp : p.Prime)
    (hb : orderOf b = p) (hnot : b ∉ Subgroup.normalizer (X : Set Y))
    {j k : ℕ} (hj : j < p) (hk : k < p) (hjk : j ≠ k) : orbA b X j ≠ orbA b X k := by
  rcases lt_or_gt_of_ne hjk with hlt | hlt
  · have := orbA_ne_aux hp hb hnot j (k - j) (by omega) (by omega)
    rwa [show j + (k - j) = k by omega] at this
  · have := orbA_ne_aux hp hb hnot k (j - k) (by omega) (by omega)
    rw [show k + (j - k) = j by omega] at this
    exact fun h => this h.symm


def diagHom {X : Subgroup Y} {b : Y} {p : ℕ}
    (hcomm : ∀ j k, j < p → k < p → j ≠ k → ∀ x ∈ orbA b X j, ∀ y ∈ orbA b X k, x * y = y * x) :
    ↥X →* Y where
  toFun x := oprod p (fun j => b ^ j * (x : Y) * (b ^ j)⁻¹)
  map_one' := by
    show oprod p (fun j => b ^ j * ((1 : ↥X) : Y) * (b ^ j)⁻¹) = 1
    simp only [Subgroup.coe_one, mul_one, mul_inv_cancel]
    exact oprod_ones p
  map_mul' x y := by
    show oprod p (fun j => b ^ j * ((x * y : ↥X) : Y) * (b ^ j)⁻¹) =
      oprod p (fun j => b ^ j * (x : Y) * (b ^ j)⁻¹) * oprod p (fun j => b ^ j * (y : Y) * (b ^ j)⁻¹)
    have e : (fun j => b ^ j * ((x * y : ↥X) : Y) * (b ^ j)⁻¹) =
        (fun j => (b ^ j * (x : Y) * (b ^ j)⁻¹) * (b ^ j * (y : Y) * (b ^ j)⁻¹)) := by
      funext j
      simp only [Subgroup.coe_mul]
      group
    rw [e]
    exact oprod_mul_of_comm fun j k hj hk hjk => hcomm j k hj hk hjk _ (mem_orbA x.2) _ (mem_orbA y.2)

theorem diag_shift {X : Subgroup Y} {b : Y} {p : ℕ} (hb : orderOf b = p) (hp0 : 0 < p)
    (hcomm : ∀ j k, j < p → k < p → j ≠ k → ∀ x ∈ orbA b X j, ∀ y ∈ orbA b X k, x * y = y * x)
    (x : Y) (hx : x ∈ X) :
    b * oprod p (fun j => b ^ j * x * (b ^ j)⁻¹) * b⁻¹ = oprod p (fun j => b ^ j * x * (b ^ j)⁻¹) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  have hbp : b ^ (m + 1) = 1 := hb ▸ pow_orderOf_eq_one b
  set F : ℕ → Y := fun j => b ^ j * x * (b ^ j)⁻¹ with hF
  have hFper : ∀ k, F (k + (m + 1)) = F k := by
    intro k
    show b ^ (k + (m + 1)) * x * (b ^ (k + (m + 1)))⁻¹ = b ^ k * x * (b ^ k)⁻¹
    rw [pow_add, hbp, mul_one]
  have hmod : ∀ i k : ℕ, i % (m + 1) ≠ k % (m + 1) → ∀ u ∈ orbA b X i, ∀ v ∈ orbA b X k,
      Commute u v := by
    intro i k hik u hu v hv
    rw [← orbA_mod hb i] at hu
    rw [← orbA_mod hb k] at hv
    exact hcomm _ _ (Nat.mod_lt _ (Nat.succ_pos m)) (Nat.mod_lt _ (Nat.succ_pos m)) hik u hu v hv
  have hcomm' : ∀ j k, j < m + 1 → k < m + 1 → j ≠ k → Commute (F (j + 1)) (F (k + 1)) := by
    intro j k hj hk hjk
    apply hmod (j + 1) (k + 1) _ _ (mem_orbA hx) _ (mem_orbA hx)
    intro heq
    apply hjk
    have h1 : j ≡ k [MOD m + 1] := Nat.ModEq.add_right_cancel' 1 heq
    unfold Nat.ModEq at h1
    rw [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hk] at h1
    exact h1
  have hper' : ∀ k, (fun j => F (j + 1)) (k + (m + 1)) = (fun j => F (j + 1)) k := by
    intro k
    show F (k + (m + 1) + 1) = F (k + 1)
    rw [show k + (m + 1) + 1 = (k + 1) + (m + 1) by ring]
    exact hFper (k + 1)
  have hrot := oprod_rot m (fun j => F (j + 1)) hper' hcomm'
  have hFF : (fun j => F (j + m + 1)) = F := by
    funext j
    show F (j + m + 1) = F j
    rw [show j + m + 1 = j + (m + 1) by ring]
    exact hFper j
  rw [hFF] at hrot
  calc b * oprod (m + 1) F * b⁻¹ = oprod (m + 1) (fun j => b * F j * b⁻¹) := conj_oprod b (m + 1) F
    _ = oprod (m + 1) (fun j => F (j + 1)) := by
      congr 1
      funext j
      show b * (b ^ j * x * (b ^ j)⁻¹) * b⁻¹ = b ^ (j + 1) * x * (b ^ (j + 1))⁻¹
      rw [pow_succ', mul_inv_rev]
      group
    _ = oprod (m + 1) F := hrot.symm

theorem OJ_eq_fin {b : Y} {X : Subgroup Y} {p : ℕ} (hb : orderOf b = p) (hp0 : 0 < p) :
    OJ b X = ⨆ i : Fin p, orbA b X (i : ℕ) := by
  apply le_antisymm
  · refine iSup_le fun j => ?_
    rw [← orbA_mod hb j]
    exact le_iSup (fun i : Fin p => orbA b X (i : ℕ)) ⟨j % p, Nat.mod_lt _ hp0⟩
  · exact iSup_le fun i => orbA_le_OJ b X i

end Case

end Components

end Input183

theorem input18_3_diag_holds : Input18_3_diag := by
  classical
  intro Y _ _ p hp L 𝓛 b hb hbN hL hcomp hcomm hcase Q hQ
  have hp0 : 0 < p := hp.pos
  have hbp : b ^ p = 1 := hb ▸ pow_orderOf_eq_one b
  have hmem : ∀ X ∈ 𝓛, ∀ j : ℕ, Input183.orbA b X j ∈ 𝓛 := fun X hX j =>
    Input183.orbA_mem_family hL hcomp hcomm hbN hX j
  have hXq : ∀ X ∈ 𝓛, CFSG.Open.IsQuasisimple ↥X := fun X hX => (hcomp X hX).2.2
  have hXL : ∀ X ∈ 𝓛, X ≤ L := fun X hX => (hcomp X hX).1
  have final : ∀ (D : Subgroup Y → Subgroup Y),
      (∀ X ∈ 𝓛, D X ≤ L ⊓ Subgroup.centralizer ({b} : Set Y)) →
      (∀ m ∈ L ⊓ Subgroup.centralizer ({b} : Set Y), ∃ d ∈ ⨆ X ∈ 𝓛, D X,
        ∃ w : Y, (∀ n ∈ L ⊓ Subgroup.centralizer ({b} : Set Y), w * n = n * w) ∧ m = d * w) →
      (∀ X ∈ 𝓛, ∀ m ∈ L ⊓ Subgroup.centralizer ({b} : Set Y),
        m ∈ Subgroup.normalizer (D X : Set Y)) →
      (∀ X ∈ 𝓛, ∃ ψ : ↥X →* Y, ψ.range = D X) →
      ∃ X ∈ 𝓛, Nonempty ((↥Q ⧸ GLAPPrimeCore p ↥Q) ⧸ Subgroup.center (↥Q ⧸ GLAPPrimeCore p ↥Q) ≃*
        (↥X ⧸ Subgroup.center ↥X)) := by
    intro D hDM hgen hDN hψ
    exact Input183.quot_diag_iso hp D hDM hgen hDN hψ hXq hQ
  have genOf : ∀ (D : Subgroup Y → Subgroup Y),
      (∀ m ∈ L ⊓ Subgroup.centralizer ({b} : Set Y), ∃ d ∈ ⨆ X ∈ 𝓛, D X,
        ∃ w ∈ L ⊓ Subgroup.centralizer (L : Set Y), m = d * w) →
      (∀ m ∈ L ⊓ Subgroup.centralizer ({b} : Set Y), ∃ d ∈ ⨆ X ∈ 𝓛, D X,
        ∃ w : Y, (∀ n ∈ L ⊓ Subgroup.centralizer ({b} : Set Y), w * n = n * w) ∧ m = d * w) := by
    intro D h m hm
    obtain ⟨d, hd, w, hw, hmw⟩ := h m hm
    refine ⟨d, hd, w, fun n hn => ?_, hmw⟩
    exact ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hw).2) n
      (Subgroup.mem_inf.1 hn).1).symm
  rcases hcase with hbC | hnot
  ·
    have hbN' : ∀ X ∈ 𝓛, b ∈ Subgroup.normalizer (X : Set Y) := fun X hX =>
      Input183.normalizer_of_commute fun s hs =>
        ((Subgroup.mem_centralizer_iff.1 hbC) s (hXL X hX hs)).symm
    have hbX : ∀ X ∈ 𝓛, ∀ j : ℕ, Input183.orbA b X j = X := fun X hX j => by
      unfold Input183.orbA
      exact gLBConj_eq_of_mem_normalizer
        ((Subgroup.normalizer _).inv_mem ((Subgroup.normalizer _).pow_mem (hbN' X hX) j))
    have hOJ : ∀ X ∈ 𝓛, Input183.OJ b X = X := fun X hX => by
      unfold Input183.OJ
      simp only [hbX X hX]
      exact iSup_const
    have hDM : ∀ X ∈ 𝓛, X ≤ L ⊓ Subgroup.centralizer ({b} : Set Y) := fun X hX x hx =>
      Subgroup.mem_inf.2 ⟨hXL X hX hx, Subgroup.mem_centralizer_singleton_iff.2
        ((Subgroup.mem_centralizer_iff.1 hbC) x (hXL X hX hx))⟩
    have hDOJ : ∀ X ∈ 𝓛, X ≤ Input183.OJ b X := fun X hX => by rw [hOJ X hX]
    have hSO : ∀ X ∈ 𝓛, ∀ o ∈ Input183.OJ b X, ∀ z ∈ L ⊓ Subgroup.centralizer (L : Set Y),
        b * o * b⁻¹ = o * z → o ∈ (fun X : Subgroup Y => X) X ⊔ (L ⊓ Subgroup.centralizer (L : Set Y)) :=
      fun X hX o ho _ _ _ => Subgroup.mem_sup_left (show o ∈ X from by rw [hOJ X hX] at ho; exact ho)
    have hDeq : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, Input183.OJ b X = Input183.OJ b X' →
        (fun X : Subgroup Y => X) X' ≤ (fun X : Subgroup Y => X) X ⊔ (L ⊓ Subgroup.centralizer (L : Set Y)) :=
      fun X hX X' hX' h => (le_of_eq (by rw [hOJ X hX, hOJ X' hX'] at h; exact h.symm)).trans le_sup_left
    obtain ⟨hC1, hC2⟩ := Input183.core_gen_normal hbp hp0 hL hmem hcomm (fun X : Subgroup Y => X)
      hDM hDOJ hSO hDeq
    exact final (fun X : Subgroup Y => X) hDM (genOf _ hC1) hC2 fun X _ => ⟨X.subtype, Subgroup.range_subtype X⟩
  ·
    have hAcomm_of : ∀ X ∈ 𝓛, ∀ j k : ℕ, j < p → k < p → j ≠ k → ∀ x ∈ Input183.orbA b X j,
        ∀ y ∈ Input183.orbA b X k, x * y = y * x := fun X hX j k hj hk hjk x hx y hy =>
      hcomm _ (hmem X hX j) _ (hmem X hX k)
        (Input183.orbA_ne_of_not_normalizer hp hb (hnot X hX) hj hk hjk) x hx y hy
    have hAL : ∀ X ∈ 𝓛, ∀ j < p, Input183.orbA b X j ≤ L := fun X hX j _ => by
      rw [hL]
      exact le_sSup (hmem X hX j)
    let Dg : Subgroup Y → Subgroup Y := fun X =>
      if h : X ∈ 𝓛 then (Input183.diagHom (hAcomm_of X h)).range else ⊥
    have hDg : ∀ X (hX : X ∈ 𝓛), Dg X = (Input183.diagHom (hAcomm_of X hX)).range :=
      fun X hX => dif_pos hX
    have hdiag_fixed : ∀ X (hX : X ∈ 𝓛) (x : ↥X),
        b * Input183.diagHom (hAcomm_of X hX) x * b⁻¹ = Input183.diagHom (hAcomm_of X hX) x :=
      fun X hX x => Input183.diag_shift hb hp0 (hAcomm_of X hX) (x : Y) x.2
    have hdiag_oprod : ∀ X (hX : X ∈ 𝓛) (x : ↥X), Input183.diagHom (hAcomm_of X hX) x =
        Input183.oprod p (fun j => b ^ j * (x : Y) * (b ^ j)⁻¹) := fun _ _ _ => rfl
    have hDM : ∀ X ∈ 𝓛, Dg X ≤ L ⊓ Subgroup.centralizer ({b} : Set Y) := by
      intro X hX d hd
      rw [hDg X hX] at hd
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hd
      refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      · rw [hdiag_oprod X hX x]
        exact Input183.oprod_mem fun j hj => hAL X hX j hj (Input183.mem_orbA x.2)
      · exact (mul_inv_eq_iff_eq_mul.1 (hdiag_fixed X hX x)).symm
    have hDOJ : ∀ X ∈ 𝓛, Dg X ≤ Input183.OJ b X := by
      intro X hX d hd
      rw [hDg X hX] at hd
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hd
      rw [hdiag_oprod X hX x]
      exact Input183.oprod_mem fun j _ => Input183.orbA_le_OJ b X j (Input183.mem_orbA x.2)
    have hSO : ∀ X ∈ 𝓛, ∀ o ∈ Input183.OJ b X, ∀ z ∈ L ⊓ Subgroup.centralizer (L : Set Y),
        b * o * b⁻¹ = o * z → o ∈ Dg X ⊔ (L ⊓ Subgroup.centralizer (L : Set Y)) := by
      intro X hX o ho z hz h
      rw [Input183.OJ_eq_fin hb hp0] at ho
      obtain ⟨x, hxX, w, hw, rfl⟩ := Input183.orbit_fixed hp0 hb hL hcomm
        (fun j hj => hmem X hX j) (fun j hj => hAL X hX j hj) (hAcomm_of X hX) hbN ho hz h
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right hw)
      rw [hDg X hX]
      exact MonoidHom.mem_range.2 ⟨⟨x, hxX⟩, rfl⟩
    have hDeq : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, Input183.OJ b X = Input183.OJ b X' →
        Dg X' ≤ Dg X ⊔ (L ⊓ Subgroup.centralizer (L : Set Y)) := by
      intro X hX X' hX' h d hd
      have hdOJ := hDOJ X' hX' hd
      rw [← h] at hdOJ
      rw [hDg X' hX'] at hd
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hd
      have hfix : b * Input183.diagHom (hAcomm_of X' hX') x * b⁻¹ =
          Input183.diagHom (hAcomm_of X' hX') x * 1 := by
        rw [mul_one]
        exact hdiag_fixed X' hX' x
      exact hSO X hX _ hdOJ 1 (L ⊓ Subgroup.centralizer (L : Set Y)).one_mem hfix
    have hψ : ∀ X ∈ 𝓛, ∃ ψ : ↥X →* Y, ψ.range = Dg X := fun X hX =>
      ⟨Input183.diagHom (hAcomm_of X hX), (hDg X hX).symm⟩
    obtain ⟨hC1, hC2⟩ := Input183.core_gen_normal hbp hp0 hL hmem hcomm Dg hDM hDOJ hSO hDeq
    exact final Dg hDM (genOf _ hC1) hC2 hψ

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
