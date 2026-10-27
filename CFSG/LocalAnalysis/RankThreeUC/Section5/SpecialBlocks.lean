module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.BinaryActionRankAlternatives
import CFSG.LocalAnalysis.RankThreeUC.Section5.FreeTranslatesBridge
import CFSG.LocalAnalysis.RankThreeUC.Section5.InvariantElemAbelianFixed
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.SpecialBlocks

open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.Section5

variable {G : Type} [Group G] [Finite G]

def radical (Q D : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ Q ∧ ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ D}

theorem mem_radical_of {Q D : Subgroup G} {x : G} (hx : x ∈ Q)
    (h : ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ D) : x ∈ radical Q D :=
  Subgroup.subset_closure ⟨hx, h⟩

theorem radical_le (Q D : Subgroup G) : radical Q D ≤ Q :=
  (Subgroup.closure_le Q).2 fun _ hx => hx.1

theorem mem_radical_iff {P Q D : Subgroup G} (hQQP : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ P)
    (hQP : Q ≤ Subgroup.centralizer (P : Set G)) {x : G} :
    x ∈ radical Q D ↔ x ∈ Q ∧ ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ D := by
  refine ⟨fun hx => ?_, fun hx => mem_radical_of hx.1 hx.2⟩
  have hcen : ∀ a ∈ Q, ∀ y ∈ Q, ∀ z ∈ Q, z * (a * y * a⁻¹ * y⁻¹) = (a * y * a⁻¹ * y⁻¹) * z :=
    fun a ha y hy z hz => (Subgroup.mem_centralizer_iff.1 (hQP hz) _ (hQQP a ha y hy)).symm
  unfold radical at hx
  induction hx using Subgroup.closure_induction with
  | mem u hu => exact hu
  | one => exact ⟨Q.one_mem, fun y _ => by simpa using D.one_mem⟩
  | mul a b _ _ ha hb =>
    refine ⟨Q.mul_mem ha.1 hb.1, fun y hy => ?_⟩
    have hc : a * (b * y * b⁻¹ * y⁻¹) = (b * y * b⁻¹ * y⁻¹) * a := hcen b hb.1 y hy a ha.1
    have key : a * b * y * (a * b)⁻¹ * y⁻¹ = (b * y * b⁻¹ * y⁻¹) * (a * y * a⁻¹ * y⁻¹) :=
      calc a * b * y * (a * b)⁻¹ * y⁻¹ = (a * (b * y * b⁻¹ * y⁻¹)) * (y * a⁻¹ * y⁻¹) := by group
        _ = ((b * y * b⁻¹ * y⁻¹) * a) * (y * a⁻¹ * y⁻¹) := by rw [hc]
        _ = (b * y * b⁻¹ * y⁻¹) * (a * y * a⁻¹ * y⁻¹) := by group
    rw [key]
    exact D.mul_mem (hb.2 y hy) (ha.2 y hy)
  | inv a _ ha =>
    refine ⟨Q.inv_mem ha.1, fun y hy => ?_⟩
    have hcomm : Commute a (a * y * a⁻¹ * y⁻¹) := hcen a ha.1 y hy a ha.1
    have hc' : (a * y * a⁻¹ * y⁻¹)⁻¹ * a = a * (a * y * a⁻¹ * y⁻¹)⁻¹ := hcomm.inv_right.eq.symm
    have key : a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ = (a * y * a⁻¹ * y⁻¹)⁻¹ :=
      calc a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ = a⁻¹ * ((a * y * a⁻¹ * y⁻¹)⁻¹ * a) := by group
        _ = a⁻¹ * (a * (a * y * a⁻¹ * y⁻¹)⁻¹) := by rw [hc']
        _ = (a * y * a⁻¹ * y⁻¹)⁻¹ := by group
    rw [key]
    exact D.inv_mem (ha.2 y hy)

theorem map_radical {Q : Subgroup G} (hQn : Q.Normal) (g : G) (D : Subgroup G) :
    (radical Q D).map (MulAut.conj g).toMonoidHom = radical Q (D.map (MulAut.conj g).toMonoidHom) := by
  unfold radical
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x₀, ⟨hx₀, h⟩, rfl⟩
    refine ⟨hQn.conj_mem x₀ hx₀ g, fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ Q := by simpa using hQn.conj_mem y hy g⁻¹
    refine ⟨x₀ * (g⁻¹ * y * g) * x₀⁻¹ * (g⁻¹ * y * g)⁻¹, h _ hy', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨hx, h⟩
    have hx' : g⁻¹ * x * g ∈ Q := by simpa using hQn.conj_mem x hx g⁻¹
    refine ⟨g⁻¹ * x * g, ⟨hx', fun y hy => ?_⟩, by group⟩
    obtain ⟨d, hd, hd'⟩ := h (g * y * g⁻¹) (hQn.conj_mem y hy g)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hd'
    have key : g⁻¹ * x * g * y * (g⁻¹ * x * g)⁻¹ * y⁻¹ =
        g⁻¹ * (x * (g * y * g⁻¹) * x⁻¹ * (g * y * g⁻¹)⁻¹) * g := by group
    rw [key, ← hd', show g⁻¹ * (g * d * g⁻¹) * g = d by group]
    exact hd

theorem mem_of_forall_mem_radical {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) {Q : Subgroup G}
    (hQQP : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ P) (hQP : Q ≤ Subgroup.centralizer (P : Set G))
    (hcenter : ∀ x ∈ Q, (∀ y ∈ Q, x * y = y * x) → x ∈ P) {x : G} (hx : x ∈ Q)
    (hxR : ∀ D ∈ Delta p P ρ, x ∈ radical Q D) : x ∈ P := by
  refine hcenter x hx fun y hy => ?_
  have h1 : x * y * x⁻¹ * y⁻¹ = 1 := FreeTranslates.eq_one_of_mem_all_Delta hc fun D hD =>
    ((mem_radical_iff hQQP hQP).1 (hxR D hD)).2 y hy
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]

theorem mem_of_commutator_mem {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) {Q : Subgroup G} (hPQ : P ≤ Q)
    (hQexp : ∀ x ∈ Q, x ^ p = 1) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    (hcyc : IsCyclic ↥(Q ⊓ Subgroup.centralizer ({b} : Set G))) {r : ℕ} (hr : r.Prime)
    (hrp : r ≠ p) (hbr : IsPGroup r ↥(Subgroup.zpowers b)) {y : G} (hy : y ∈ Q)
    (hby : b * y * b⁻¹ * y⁻¹ ∈ P) : y ∈ P := by
  have hS := hc.oddPrimeClassTwoAction.setting
  have hPn : P.Normal := hc.faithfulBinaryIrreducibleAction.normal
  haveI : Fact p.Prime := ⟨hS.prime⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hCQ := InvariantElemAbelianFixed.inf_centralizer_eq hc hPQ hQexp hb hb1 hcyc
  let St : Subgroup G :=
    { carrier := {a | a * y * a⁻¹ * y⁻¹ ∈ P}
      one_mem' := by simp
      mul_mem' := fun {a₁ a₂} h₁ h₂ => by
        have h3 := P.mul_mem (hPn.conj_mem _ h₂ a₁) h₁
        have e3 : a₁ * (a₂ * y * a₂⁻¹ * y⁻¹) * a₁⁻¹ * (a₁ * y * a₁⁻¹ * y⁻¹) =
            a₁ * a₂ * y * (a₁ * a₂)⁻¹ * y⁻¹ := by group
        rw [e3] at h3
        exact h3
      inv_mem' := fun {a} h => by
        have h3 := hPn.conj_mem _ (P.inv_mem h) a⁻¹
        have e3 : a⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * a⁻¹⁻¹ = a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ := by group
        rw [e3] at h3
        exact h3 }
  have hbSt : Subgroup.zpowers b ≤ St := (Subgroup.zpowers_le (H := St)).2 hby
  have hrP : ¬ r ∣ Nat.card P := by
    intro h
    obtain ⟨k, hk⟩ := hS.pGroup.exists_card_eq
    rw [hk] at h
    exact hrp ((Nat.prime_dvd_prime_iff_eq hr hS.prime).1 (hr.dvd_of_dvd_pow h))
  obtain ⟨c, hcy, hcfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed r hbr
    ((MulAut.conj : G →* MulAut G).comp (Subgroup.zpowers b).subtype) P hrP y).1 (by
      intro a x hx
      have ha : (a : G) * y * (a : G)⁻¹ * y⁻¹ ∈ P := hbSt a.2
      have h3 := P.mul_mem (hPn.conj_mem _ hx (a : G)) ha
      have e3 : (a : G) * (x * y⁻¹) * (a : G)⁻¹ * ((a : G) * y * (a : G)⁻¹ * y⁻¹) =
          (a : G) * x * (a : G)⁻¹ * y⁻¹ := by group
      rw [e3] at h3
      simpa using h3)
  have hbc : b * c * b⁻¹ = c := by simpa using hcfix ⟨b, Subgroup.mem_zpowers b⟩
  have hcQ : c ∈ Q := by simpa using Q.mul_mem (hPQ hcy) hy
  have hcC : c ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    calc b * c = b * c * b⁻¹ * b := by group
      _ = c * b := by rw [hbc]
  have hcP : c ∈ P := by
    have h4 : c ∈ Q ⊓ Subgroup.centralizer ({b} : Set G) := ⟨hcQ, hcC⟩
    rw [← hCQ] at h4
    exact h4.1
  simpa using P.mul_mem (P.inv_mem hcy) hcP

theorem map_mem_fixedSubmodule {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {D : Subgroup G} {g : G} (hg : ∀ d ∈ D, d * g = g * d) {v : V}
    (hv : v ∈ fixedSubmodule ρ D) : ρ g v ∈ fixedSubmodule ρ D := by
  rw [QuadraticSetConjugationTransport.mem_fixedSubmodule_iff] at hv ⊢
  intro d hd
  rw [← Module.End.mul_apply, ← map_mul, hg d hd, map_mul, Module.End.mul_apply, hv d hd]

theorem le_sup_zpowers {D P : Subgroup G} {p : ℕ} (hp : p.Prime) (hDP : D ≤ P)
    (hidx : D.relIndex P = p) {w : G} (hwP : w ∈ P) (hwD : w ∉ D) :
    P ≤ D ⊔ Subgroup.zpowers w := by
  have hKP : D ⊔ Subgroup.zpowers w ≤ P := sup_le hDP (Subgroup.zpowers_le.2 hwP)
  have hmul := Subgroup.relIndex_mul_relIndex D (D ⊔ Subgroup.zpowers w) P le_sup_left hKP
  rw [hidx] at hmul
  rcases (Nat.dvd_prime hp).1 (Dvd.intro_left _ hmul) with h | h
  · exact Subgroup.relIndex_eq_one.1 h
  · exfalso
    rw [h] at hmul
    have h1 : D.relIndex (D ⊔ Subgroup.zpowers w) = 1 :=
      Nat.eq_of_mul_eq_mul_right hp.pos (hmul.trans (one_mul p).symm)
    exact hwD (Subgroup.relIndex_eq_one.1 h1 (Subgroup.mem_sup_right (Subgroup.mem_zpowers w)))

theorem mem_of_fixes {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) {D : Subgroup G} (hD : D ∈ Delta p P ρ)
    {w : G} (hwP : w ∈ P) (hw : ∀ v ∈ fixedSubmodule ρ D, ρ w v = v) : w ∈ D := by
  by_contra hwD
  have hS := hc.oddPrimeClassTwoAction.setting
  let K : Subgroup G :=
    { carrier := {g | ∀ v ∈ fixedSubmodule ρ D, ρ g v = v}
      one_mem' := fun v _ => by simp
      mul_mem' := fun {a b} ha hb v hv => by
        rw [map_mul, Module.End.mul_apply, hb v hv, ha v hv]
      inv_mem' := fun {a} ha v hv =>
        calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha v hv]
          _ = v := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hDK : D ≤ K := fun d hd v hv =>
    (QuadraticSetConjugationTransport.mem_fixedSubmodule_iff ρ D v).1 hv d hd
  have hPK : P ≤ K := (le_sup_zpowers hS.prime hD.1 hD.2.1 hwP hwD).trans
    (sup_le hDK (Subgroup.zpowers_le.2 hw))
  apply hD.2.2
  rw [eq_bot_iff, ← InvariantElemAbelianFixed.fixedSubmodule_eq_bot hc]
  intro v hv
  exact (QuadraticSetConjugationTransport.mem_fixedSubmodule_iff ρ P v).2 fun g hg => hPK hg v hv

theorem fixes_of_finrank_le_two {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (g : Module.End (ZMod 2) M) (hg : g ^ p = 1)
    {W : Submodule (ZMod 2) M} (hW : ∀ w ∈ W, g w ∈ W)
    (hdim : Module.finrank (ZMod 2) (W.map (g - 1)) ≤ 2) : ∀ w ∈ W, g w = w := by
  set U := W.map (g - 1) with hUdef
  have hU : ∀ u ∈ U, g u ∈ U := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨g w, hW w hw, ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
  have key : ∀ z : M, (g ^ (p - 1)) (g z) = z := by
    intro z
    rw [← Module.End.mul_apply, ← pow_succ, Nat.sub_add_cancel hp.one_le, hg, Module.End.one_apply]
  have hinj : Function.Injective g := fun x y hxy => by rw [← key x, ← key y, hxy]
  let f : ↥U → ↥U := fun u => ⟨g u, hU u u.2⟩
  have hfinj : Function.Injective f := fun u v huv => by
    have h' := congrArg Subtype.val huv
    exact Subtype.ext (hinj h')
  let σ : Equiv.Perm ↥U := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfinj)
  have hσpow : ∀ (n : ℕ) (u : ↥U), (((σ ^ n) u : ↥U) : M) = (g ^ n) u := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Module.End.mul_apply, ← ih u]
      rfl
  have hσp : σ ^ p = 1 := by
    refine Equiv.ext fun u => Subtype.ext ?_
    rw [hσpow p u, hg]
    rfl
  have hcardU : Nat.card ↥U ≤ 4 := by
    rw [← FiniteField.pow_finrank_eq_natCard 2 ↥U]
    calc 2 ^ Module.finrank (ZMod 2) ↥U ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hdim
      _ = 4 := by norm_num
  have hσ1 : σ = 1 := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hσp) with h | h
    · exact orderOf_eq_one_iff.1 h
    · exfalso
      have h2 : p ∣ (Nat.card ↥U).factorial := by
        rw [← h, ← Nat.card_perm]
        exact orderOf_dvd_natCard σ
      have h3 := (Nat.Prime.dvd_factorial hp).1 h2
      omega
  have hfixU : ∀ u ∈ U, g u = u := by
    intro u hu
    have h5 := congrArg (fun τ : Equiv.Perm ↥U => ((τ ⟨u, hu⟩ : ↥U) : M)) hσ1
    exact h5
  intro w hw
  set n := g w - w with hn
  have hgn : g n = n := hfixU n ⟨w, hw, by simp [hn]⟩
  have hgw : g w = w + n := by rw [hn]; abel
  have hpow : ∀ k : ℕ, (g ^ k) w = w + k • n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_add, map_nsmul, hgn, hgw, succ_nsmul]
      abel
  have h1 : p • n = 0 := by
    have h6 := hpow p
    rw [hg, Module.End.one_apply] at h6
    simpa using h6.symm
  have h2 : p • n = n := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2),
      ZMod.natCast_eq_one_iff_odd.2 (hp.odd_of_ne_two (by omega)), one_smul]
  rw [hgw, ← h2, h1, add_zero]

theorem finrank_block {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) {Q : Subgroup G} (hQn : Q.Normal)
    (hQP : Q ≤ Subgroup.centralizer (P : Set G)) (hQexp : ∀ x ∈ Q, x ^ p = 1)
    (hQQP : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ P) {t : G} (ht2 : t * t = 1)
    (htP : t ∈ Subgroup.centralizer (P : Set G)) {D : Subgroup G} (hD : D ∈ Delta p P ρ)
    {y : G} (hy : y ∈ Q) (hyD : y * t * y⁻¹ * t⁻¹ ∉ radical Q D) :
    1 ≤ Module.finrank (ZMod 2) ((fixedSubmodule ρ D).map (ρ t - 1)) ∧
      (5 ≤ p → 2 ≤ Module.finrank (ZMod 2) ((fixedSubmodule ρ D).map (ρ t - 1))) := by
  classical
  have hS := hc.oddPrimeClassTwoAction.setting
  have hDP : D ≤ P := hD.1
  set W := fixedSubmodule ρ D with hWdef
  have hpres : ∀ g ∈ Subgroup.centralizer (P : Set G), ∀ v ∈ W, ρ g v ∈ W := fun g hg v hv =>
    map_mem_fixedSubmodule ρ (fun d hd => Subgroup.mem_centralizer_iff.1 hg d (hDP hd)) hv
  set c := y * t * y⁻¹ * t⁻¹ with hcdef
  have hcQ : c ∈ Q := by
    have h1 := Q.mul_mem hy (hQn.conj_mem y⁻¹ (Q.inv_mem hy) t)
    simpa [hcdef, mul_assoc] using h1
  obtain ⟨z, hzQ, hzD⟩ : ∃ z ∈ Q, c * z * c⁻¹ * z⁻¹ ∉ D := by
    by_contra hno
    push Not at hno
    exact hyD (mem_radical_of hcQ hno)
  have hcW : ∃ v ∈ W, ρ c v ≠ v := by
    by_contra hno
    push Not at hno
    apply hzD
    refine mem_of_fixes hc hD (hQQP c hcQ z hzQ) fun v hv => ?_
    have hz' : ρ z⁻¹ v ∈ W := hpres _ (hQP (Q.inv_mem hzQ)) v hv
    have hc' : ρ c⁻¹ (ρ z⁻¹ v) = ρ z⁻¹ v :=
      calc ρ c⁻¹ (ρ z⁻¹ v) = ρ c⁻¹ (ρ c (ρ z⁻¹ v)) := by rw [hno _ hz']
        _ = ρ z⁻¹ v := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    calc ρ (c * z * c⁻¹ * z⁻¹) v = ρ c (ρ z (ρ c⁻¹ (ρ z⁻¹ v))) := by
          simp only [map_mul, Module.End.mul_apply]
      _ = ρ c (ρ z (ρ z⁻¹ v)) := by rw [hc']
      _ = ρ c v := by
          rw [← Module.End.mul_apply (ρ z), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      _ = v := hno v hv
  set Tt := W.map (ρ t - 1) with hTdef
  have htW : ∀ v ∈ W, ρ t v ∈ W := hpres t htP
  have hyW : ∀ v ∈ W, ρ y⁻¹ v ∈ W := hpres _ (hQP (Q.inv_mem hy))
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hincl : W.map (ρ c - 1) ≤ Tt.map (ρ y) ⊔ Tt := by
    rintro _ ⟨v, hv, rfl⟩
    have hρc : ρ c v = ρ y (ρ t (ρ y⁻¹ (ρ t v))) := by
      rw [hcdef, htinv]
      simp only [map_mul, Module.End.mul_apply]
    have hyy : ρ y (ρ y⁻¹ (ρ t v)) = ρ t v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have hdecomp : (ρ c - 1) v = ρ y ((ρ t - 1) (ρ y⁻¹ (ρ t v))) + (ρ t - 1) v := by
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hρc, hyy]
      abel
    rw [hdecomp]
    exact Submodule.add_mem_sup ⟨_, ⟨ρ y⁻¹ (ρ t v), hyW _ (htW v hv), rfl⟩, rfl⟩ ⟨v, hv, rfl⟩
  have hdim : Module.finrank (ZMod 2) (W.map (ρ c - 1)) ≤ 2 * Module.finrank (ZMod 2) Tt :=
    calc Module.finrank (ZMod 2) (W.map (ρ c - 1)) ≤ Module.finrank (ZMod 2) ↥(Tt.map (ρ y) ⊔ Tt) :=
          Submodule.finrank_mono hincl
      _ ≤ Module.finrank (ZMod 2) (Tt.map (ρ y)) + Module.finrank (ZMod 2) Tt :=
          Submodule.finrank_add_le_finrank_add_finrank _ _
      _ ≤ Module.finrank (ZMod 2) Tt + Module.finrank (ZMod 2) Tt :=
          Nat.add_le_add_right (Submodule.finrank_map_le _ _) _
      _ = 2 * Module.finrank (ZMod 2) Tt := by ring
  obtain ⟨v, hv, hcv⟩ := hcW
  refine ⟨?_, fun hp5 => ?_⟩
  · by_contra h0
    have h0' : Module.finrank (ZMod 2) (W.map (ρ c - 1)) = 0 := by omega
    rw [Submodule.finrank_eq_zero] at h0'
    apply hcv
    have h7 : (ρ c - 1) v ∈ W.map (ρ c - 1) := ⟨v, hv, rfl⟩
    rw [h0', Submodule.mem_bot, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h7
    exact h7
  · by_contra h1
    exact hcv (fixes_of_finrank_le_two hS.prime hp5 (ρ c)
      (by rw [← map_pow, hQexp c hcQ, map_one]) (hpres c (hQP hcQ)) (by omega) v hv)

theorem card_mul_le {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) {t : G}
    (htP : t ∈ Subgroup.centralizer (P : Set G)) {Γ : Set (Subgroup G)} (hΓ : Γ ⊆ Delta p P ρ)
    {m : ℕ} (hm : ∀ D ∈ Γ, m ≤ Module.finrank (ZMod 2) ((fixedSubmodule ρ D).map (ρ t - 1))) :
    m * Nat.card ↥Γ ≤ Module.finrank (ZMod 2) (V ⧸ fixedSubmodule ρ (Subgroup.zpowers t)) := by
  classical
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  haveI : Fintype ↥Γ := Fintype.ofFinite _
  have hind :=
    (isInternal_hyperplane_fixedSubmodule_of_binary_rank_counterexample hc).submodule_iSupIndep
  let f : ↥Γ → ↥(Delta p P ρ) := fun D => ⟨D.1, hΓ D.2⟩
  have hfinj : Function.Injective f := fun D₁ D₂ h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  have hTle : (fun D : ↥Γ => (fixedSubmodule ρ D.1).map (ρ t - 1)) ≤
      (fun D : ↥(Delta p P ρ) => fixedSubmodule ρ (D : Subgroup G)) ∘ f := by
    intro D x hx
    obtain ⟨v, hv, rfl⟩ := hx
    have hDP : (D : Subgroup G) ≤ P := (hΓ D.2).1
    have htv := map_mem_fixedSubmodule ρ
      (fun d hd => Subgroup.mem_centralizer_iff.1 htP d (hDP hd)) hv
    rw [LinearMap.sub_apply, Module.End.one_apply]
    exact Submodule.sub_mem _ htv hv
  have hindT : iSupIndep fun D : ↥Γ => (fixedSubmodule ρ D.1).map (ρ t - 1) :=
    (hind.comp hfinj).mono hTle
  have hsum := TauCeti.finrank_iSup_eq_sum_finrank_of_iSupIndep hindT
  have hsup : (⨆ D : ↥Γ, (fixedSubmodule ρ D.1).map (ρ t - 1)) ≤ LinearMap.range (ρ t - 1) :=
    iSup_le fun _ => LinearMap.map_le_range
  rw [← commRank_eq_fixedQuot_finrank]
  calc m * Nat.card ↥Γ = ∑ _D : ↥Γ, m := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card, mul_comm]
    _ ≤ ∑ D : ↥Γ, Module.finrank (ZMod 2) ((fixedSubmodule ρ D.1).map (ρ t - 1)) :=
        Finset.sum_le_sum fun D _ => hm D.1 D.2
    _ = Module.finrank (ZMod 2) ↥(⨆ D : ↥Γ, (fixedSubmodule ρ D.1).map (ρ t - 1)) := hsum.symm
    _ ≤ commRank ρ t := Submodule.finrank_mono hsup

end CFSG.LocalAnalysis.RankThreeUC.Section5.SpecialBlocks
