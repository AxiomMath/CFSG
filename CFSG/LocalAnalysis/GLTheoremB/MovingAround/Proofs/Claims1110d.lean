module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110c
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltFix
public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownComp

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110d

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut innerAut Fi22Facts IsFiTwentyTwo)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  (conj_mem_gLAPPrimeCoreOf gLAPPrimeCoreOf_le mem_gLAPPrimeCoreOf_iff card_gLAPPrimeCoreOf_coprime)
open scoped Pointwise

section CentMod

variable {G : Type} [Group G]

@[expose] def centMod (p : ℕ) (X J : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ X ∧ ∀ y ∈ J, x * y * x⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf p X}
  mul_mem' := by
    rintro x x' ⟨hxX, hx⟩ ⟨hx'X, hx'⟩
    refine ⟨X.mul_mem hxX hx'X, fun y hy => ?_⟩
    have h1 := conj_mem_gLAPPrimeCoreOf p X hxX (hx' y hy)
    have hm := (GLAPPrimeCoreOf p X).mul_mem h1 (hx y hy)
    have e' : x * x' * y * (x * x')⁻¹ * y⁻¹ =
        x * (x' * y * x'⁻¹ * y⁻¹) * x⁻¹ * (x * y * x⁻¹ * y⁻¹) := by group
    rw [e']
    exact hm
  one_mem' := ⟨X.one_mem, fun y _ => by simp⟩
  inv_mem' := by
    rintro x ⟨hxX, hx⟩
    refine ⟨X.inv_mem hxX, fun y hy => ?_⟩
    have h1 := conj_mem_gLAPPrimeCoreOf p X (X.inv_mem hxX)
      ((GLAPPrimeCoreOf p X).inv_mem (hx y hy))
    have e' : x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ = x⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e']
    exact h1

theorem mem_centMod {p : ℕ} {X J : Subgroup G} {x : G} :
    x ∈ centMod p X J ↔ x ∈ X ∧ ∀ y ∈ J, x * y * x⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf p X := Iff.rfl

theorem centMod_anti {p : ℕ} {X J J' : Subgroup G} (h : J ≤ J') : centMod p X J' ≤ centMod p X J :=
  fun _ hx => ⟨hx.1, fun y hy => hx.2 y (h hy)⟩

theorem comm_mem_core_symm {p : ℕ} {X : Subgroup G} {x y : G}
    (h : x * y * x⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf p X) : y * x * y⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf p X := by
  have h1 := (GLAPPrimeCoreOf p X).inv_mem h
  have e' : (x * y * x⁻¹ * y⁻¹)⁻¹ = y * x * y⁻¹ * x⁻¹ := by group
  rwa [e'] at h1

theorem le_centMod_comm {p : ℕ} {X H J : Subgroup G} (hJX : J ≤ X) (h : H ≤ centMod p X J) :
    J ≤ centMod p X H :=
  fun y hy => ⟨hJX hy, fun x hx => comm_mem_core_symm ((h hx).2 y hy)⟩

theorem core_le_centMod (p : ℕ) {X J : Subgroup G} (hJX : J ≤ X) :
    GLAPPrimeCoreOf p X ≤ centMod p X J := by
  intro o ho
  refine ⟨gLAPPrimeCoreOf_le p X ho, fun y hy => ?_⟩
  have h1 := conj_mem_gLAPPrimeCoreOf p X (hJX hy) ((GLAPPrimeCoreOf p X).inv_mem ho)
  have e' : o * y * o⁻¹ * y⁻¹ = o * (y * o⁻¹ * y⁻¹) := by group
  rw [e']
  exact (GLAPPrimeCoreOf p X).mul_mem ho h1

theorem mem_normalizer_sup_core {p : ℕ} {X N : Subgroup G} {j : G} (hj : j ∈ centMod p X N) :
    j ∈ Subgroup.normalizer ((N ⊔ GLAPPrimeCoreOf p X : Subgroup G) : Set G) := by
  have key : ∀ j' ∈ centMod p X N, ∀ n ∈ N ⊔ GLAPPrimeCoreOf p X,
      j' * n * j'⁻¹ ∈ N ⊔ GLAPPrimeCoreOf p X := by
    intro j' hj' n hn
    have hle : N ⊔ GLAPPrimeCoreOf p X ≤
        (N ⊔ GLAPPrimeCoreOf p X).comap (MulAut.conj j').toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun o ho => ?_)
      · show j' * y * j'⁻¹ ∈ N ⊔ GLAPPrimeCoreOf p X
        have e' : j' * y * j'⁻¹ = (j' * y * j'⁻¹ * y⁻¹) * y := by group
        rw [e']
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hj'.2 y hy)) (Subgroup.mem_sup_left hy)
      · show j' * o * j'⁻¹ ∈ N ⊔ GLAPPrimeCoreOf p X
        exact Subgroup.mem_sup_right (conj_mem_gLAPPrimeCoreOf p X hj'.1 ho)
    exact hle hn
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · exact key j hj n
  · intro hn
    have := key j⁻¹ ((centMod p X N).inv_mem hj) _ hn
    simpa [mul_assoc] using this

theorem core_inf_le {p : ℕ} [Finite G] {X J : Subgroup G} (hJX : J ≤ X) :
    GLAPPrimeCoreOf p X ⊓ J ≤ GLAPPrimeCoreOf p J := by
  intro y hy
  obtain ⟨hyO, hyJ⟩ := Subgroup.mem_inf.1 hy
  set T : Subgroup ↥J := (GLAPPrimeCoreOf p X ⊓ J).subgroupOf J with hT
  have hTn : T.Normal := by
    refine ⟨fun t ht g => ?_⟩
    rw [hT, Subgroup.mem_subgroupOf] at ht ⊢
    obtain ⟨htO, htJ⟩ := Subgroup.mem_inf.1 ht
    refine Subgroup.mem_inf.2 ⟨?_, (g * t * g⁻¹ : ↥J).2⟩
    exact conj_mem_gLAPPrimeCoreOf p X (hJX g.2) htO
  have hTc : Nat.Coprime p (Nat.card T) := by
    have h1 : Nat.card T = Nat.card ↥(GLAPPrimeCoreOf p X ⊓ J) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [h1]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (card_gLAPPrimeCoreOf_coprime p X)
  have hTle : T ≤ GLAPPrimeCore p ↥J := le_sSup ⟨hTn, hTc⟩
  have hyT : (⟨y, hyJ⟩ : ↥J) ∈ T := by
    rw [hT, Subgroup.mem_subgroupOf]
    exact hy
  exact (mem_gLAPPrimeCoreOf_iff p J y).2 ⟨hyJ, hTle hyT⟩

theorem mem_core_of_center_eq_bot {p : ℕ} {J : Subgroup G}
    (hZ : Subgroup.center (barOf p J) = ⊥) {v : G} (hvJ : v ∈ J)
    (hv : ∀ y ∈ J, v * y * v⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf p J) : v ∈ GLAPPrimeCoreOf p J := by
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥J) with hπ
  have hc : π ⟨v, hvJ⟩ ∈ Subgroup.center (barOf p J) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨⟨y, hyJ⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨hmem, hc'⟩ := (mem_gLAPPrimeCoreOf_iff p J _).1 (hv y hyJ)
    have h1 : π (⟨v, hvJ⟩ * ⟨y, hyJ⟩ * ⟨v, hvJ⟩⁻¹ * ⟨y, hyJ⟩⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hc'
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 : π ⟨v, hvJ⟩ * π ⟨y, hyJ⟩ = π ⟨y, hyJ⟩ * π ⟨v, hvJ⟩ := by
      have := congrArg (· * (π ⟨y, hyJ⟩ * π ⟨v, hvJ⟩)) h1
      simpa [mul_assoc] using this
    exact h2.symm
  rw [hZ, Subgroup.mem_bot] at hc
  exact (mem_gLAPPrimeCoreOf_iff p J v).2 ⟨hvJ, (QuotientGroup.eq_one_iff _).1 hc⟩

end CentMod

section Join

variable {G : Type} [Group G] [Finite G]

theorem le_centMod_of_ne {p : ℕ} (hp : p.Prime) {X J J' : Subgroup G} (hJ : GLAPComponent p X J)
    (hJ' : GLAPComponent p X J') (hne : J' ≠ J) : J' ≤ centMod p X J := by
  have hle := Claims1110.le_centBar_of_ne' hp hJ hJ' hne
  intro y hy
  obtain ⟨hyX, -, hyc⟩ := Claims1110.mem_centBar_iff_forall'.1 (hle hy)
  exact ⟨hyX, fun z hz => CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal p
    hJ.2.1 (hyc z hz)⟩

theorem mem_core_of_mem_iSup {p : ℕ} (hp : p.Prime) {X : Subgroup G} (𝒥 : Finset (Subgroup G))
    (h𝒥 : ∀ J ∈ 𝒥, GLAPComponent p X J) (hZ : ∀ J ∈ 𝒥, Subgroup.center (barOf p J) = ⊥) :
    ∀ x ∈ (⨆ J ∈ 𝒥, J) ⊔ GLAPPrimeCoreOf p X, (∀ J ∈ 𝒥, x ∈ centMod p X J) →
      x ∈ GLAPPrimeCoreOf p X := by
  classical
  induction 𝒥 using Finset.induction_on with
  | empty =>
    intro x hx _
    simpa using hx
  | insert J 𝒥' hJ𝒥 ih =>
    intro x hx hc
    have h𝒥' : ∀ J' ∈ 𝒥', GLAPComponent p X J' := fun J' hJ' => h𝒥 J' (Finset.mem_insert_of_mem hJ')
    have hZ' : ∀ J' ∈ 𝒥', Subgroup.center (barOf p J') = ⊥ :=
      fun J' hJ' => hZ J' (Finset.mem_insert_of_mem hJ')
    have hJc : GLAPComponent p X J := h𝒥 J (Finset.mem_insert_self J 𝒥')
    have hJX : J ≤ X := hJc.1
    set N' : Subgroup G := ⨆ J' ∈ 𝒥', J' with hN'
    set O : Subgroup G := GLAPPrimeCoreOf p X with hO
    have hN'X : N' ≤ X := iSup₂_le fun J' hJ' => (h𝒥' J' hJ').1
    have hN'O : N' ⊔ O ≤ centMod p X J := by
      refine sup_le (iSup₂_le fun J' hJ' => ?_) (core_le_centMod p hJX)
      exact le_centMod_of_ne hp hJc (h𝒥' J' hJ') (fun h => hJ𝒥 (h ▸ hJ'))
    have hJN : J ≤ Subgroup.normalizer ((N' ⊔ O : Subgroup G) : Set G) := fun j hj =>
      mem_normalizer_sup_core (centMod_anti le_sup_left (le_centMod_comm hJX hN'O hj))
    have hx' : x ∈ (N' ⊔ O) ⊔ J := by
      have e : (⨆ J'' ∈ insert J 𝒥', J'') ⊔ O = (N' ⊔ O) ⊔ J := by
        rw [Finset.iSup_insert, sup_comm J, sup_right_comm]
      rw [← e]
      exact hx
    have hmem : x ∈ ((N' ⊔ O : Subgroup G) : Set G) * (J : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (N' ⊔ O) J hJN]
      exact hx'
    obtain ⟨u, hu, v, hv, rfl⟩ := hmem
    have huc : u ∈ centMod p X J := hN'O hu
    have hvc : v ∈ centMod p X J := by
      have := (centMod p X J).mul_mem ((centMod p X J).inv_mem huc) (hc J (Finset.mem_insert_self J 𝒥'))
      simpa using this
    have hvO : v ∈ O := by
      refine CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal p hJc.2.1
        (mem_core_of_center_eq_bot (hZ J (Finset.mem_insert_self J 𝒥')) hv fun y hy => ?_)
      exact core_inf_le hJX (Subgroup.mem_inf.2 ⟨hvc.2 y hy,
        J.mul_mem (J.mul_mem (J.mul_mem hv hy) (J.inv_mem hv)) (J.inv_mem hy)⟩)
    have huv : u * v ∈ N' ⊔ O := Subgroup.mul_mem _ hu (Subgroup.mem_sup_right hvO)
    exact ih h𝒥' hZ' (u * v) huv fun J' hJ' => hc J' (Finset.mem_insert_of_mem hJ')

theorem glaPComponent_ne_bot' {p : ℕ} {X L : Subgroup G} (h : GLAPComponent p X L) : L ≠ ⊥ := by
  intro hL
  have h3 := h.2.2.1
  subst hL
  have hbot : ((⊥ : Subgroup G).subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) = ⊥ := by
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  rw [hbot] at h3
  obtain ⟨-, hsimple⟩ := h3.2.2
  have := hsimple.toNontrivial
  have hss : Subsingleton (↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) ⧸
      Subgroup.center ↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X))) := inferInstance
  exact (not_subsingleton_iff_nontrivial.2 inferInstance) hss

theorem eq_one_of_mem_core {p : ℕ} [Fact p.Prime] {X : Subgroup G} {x : G}
    (hx : x ∈ GLAPPrimeCoreOf p X) {k : ℕ} (hxk : x ^ (p ^ k) = 1) : x = 1 :=
  Claims1110.eq_one_of_dvd_coprime ((card_gLAPPrimeCoreOf_coprime p X).pow_left k)
    (orderOf_dvd_of_pow_eq_one hxk) (Subgroup.orderOf_dvd_natCard _ hx)

end Join

section Ke

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut_mk)

theorem cg2_eq_inf (e a : G) : Cg2 e a = Cg a ⊓ Cg e := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  tauto

theorem ke_facts (hI1421 : Input14_21) (hF : Fi22Facts) (h119 : Lemma119Statement)
    {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m 5 B M E A a K)
    (hfi : IsSporType .Fi22 (barOf 5 K)) {e : G} (heA : e ∈ E ⊓ A) (he1 : e ≠ 1) :
    GLAPComponent 5 (K ⊓ Cg e) (GLAPLayer 5 (K ⊓ Cg e)) ∧
      IsAltType 5 (barOf 5 (GLAPLayer 5 (K ⊓ Cg e))) := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hS := h.toCex117Base.toSec11.toSec10Fails
  have hsc := lemma104_ii_holds hS h.pair
  obtain ⟨-, hN, hfaith, hinn⟩ := h119 h
  have heN : e ∈ Subgroup.normalizer (K : Set G) := hN heA
  obtain ⟨k, hkK, hkc⟩ := hinn e heA
  obtain ⟨hZ, -, -, -⟩ := hF (barOf 5 K) hfi
  set O' : Subgroup ↥K := GLAPPrimeCore 5 ↥K with hO'
  set π : ↥K →* ↥K ⧸ O' := QuotientGroup.mk' O' with hπ
  have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hkK
  have hbe : barAut 5 K ⟨e, heN⟩ = MulAut.conj (π ⟨k, hkK⟩) := by
    obtain ⟨-, hcN, hc1⟩ := Claims1110.mem_centBar_iff'.1 hkc
    have hsplit : (⟨e, heN⟩ : ↥(Subgroup.normalizer (K : Set G))) = ⟨k, hkN⟩ * ⟨k⁻¹ * e, hcN⟩ :=
      Subtype.ext (by simp)
    rw [hsplit, map_mul, hc1, mul_one, Claims1110.barAut_of_mem hkK]
    rfl
  set kb : ↥K ⧸ O' := π ⟨k, hkK⟩ with hkb
  have he5 : e ^ 5 = 1 := hsc.2.2.1.2 e (Subgroup.mem_inf.1 heA).2
  have hconj_one : ∀ z : ↥K ⧸ O', MulAut.conj z = 1 → z = 1 := by
    intro z hz
    have hc : z ∈ Subgroup.center (↥K ⧸ O') := by
      rw [Subgroup.mem_center_iff]
      intro w
      have h1 := congrArg (fun φ : MulAut (↥K ⧸ O') => φ w) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm
    have hZ' : Subgroup.center (↥K ⧸ O') = ⊥ := hZ
    rw [hZ', Subgroup.mem_bot] at hc
    exact hc
  have hkb5 : kb ^ 5 = 1 := by
    refine hconj_one _ ?_
    rw [map_pow, ← hbe, ← map_pow]
    have : (⟨e, heN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 5 = 1 := Subtype.ext (by simpa using he5)
    rw [this, map_one]
  have hkb1 : kb ≠ 1 := by
    intro h1
    apply he1
    refine hfaith e heA (Claims1110.mem_centBar_iff'.2 ⟨trivial, heN, ?_⟩)
    rw [hbe, h1, map_one]
  have hkbo : orderOf kb = 5 := orderOf_eq_prime hkb5 hkb1
  obtain ⟨ψ⟩ := hI1421 (barOf 5 K) hfi kb hkbo
  set Lb : Subgroup (↥K ⧸ O') := GLAPLayer 5 (Subgroup.centralizer ({kb} : Set (↥K ⧸ O'))) with hLb
  haveI hLbs : IsSimpleGroup ↥Lb := ψ.isSimpleGroup
  have hLc : Nat.card ↥Lb = 60 := by
    rw [Nat.card_congr ψ.toEquiv]
    exact CFSG.GH74.GLS.LU.Local.Five.nat_card_alternatingGroup_five
  set C' : Subgroup ↥K := (Cg e).subgroupOf K with hC'
  have hbar : ∀ (j : ℤ) (y : ↥K), π ⟨e ^ j * (y : G) * (e ^ j)⁻¹,
      (Subgroup.mem_normalizer_iff.1 (Subgroup.zpow_mem _ heN j) y).1 y.2⟩ = kb ^ j * π y * (kb ^ j)⁻¹ := by
    intro j y
    have h1 := barAut_mk 5 K ⟨e ^ j, Subgroup.zpow_mem _ heN j⟩ y
    have h2 : barAut 5 K ⟨e ^ j, Subgroup.zpow_mem _ heN j⟩ = MulAut.conj (kb ^ j) := by
      have : (⟨e ^ j, Subgroup.zpow_mem _ heN j⟩ : ↥(Subgroup.normalizer (K : Set G))) =
          (⟨e, heN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ j := Subtype.ext (by simp)
      rw [this, map_zpow, hbe, ← map_zpow]
    rw [h2, MulAut.conj_apply] at h1
    exact h1.symm
  have hCmap : C'.map π = Subgroup.centralizer ({kb} : Set (↥K ⧸ O')) := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      have hye : e * (y : G) * e⁻¹ = y := by
        have h1 : (y : G) * e = e * y := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 hy)
        rw [← h1]
        group
      have h2 := hbar 1 y
      simp only [zpow_one] at h2
      have h3 : (⟨e * (y : G) * e⁻¹, (Subgroup.mem_normalizer_iff.1 heN y).1 y.2⟩ : ↥K) = y :=
        Subtype.ext hye
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h4 : π y = kb * π y * kb⁻¹ := by
        rw [← h2]
        exact congrArg π h3.symm
      calc π y * kb = (kb * π y * kb⁻¹) * kb := by rw [← h4]
        _ = kb * π y := by group
    · intro yb hyb
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O' yb
      have hcomm : Commute kb (π y) := (Subgroup.mem_centralizer_singleton_iff.1 hyb).symm
      set O := GLAPPrimeCoreOf 5 K with hO
      have hOcop := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.card_gLAPPrimeCoreOf_coprime 5 K
      have hVX : Subgroup.zpowers e ≤ Subgroup.normalizer (O : Set G) :=
        (Subgroup.zpowers_le).2
          (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_normalizer_gLAPPrimeCoreOf 5 heN)
      have hzX : (y : G) ∈ Subgroup.normalizer (O : Set G) :=
        CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.le_normalizer_gLAPPrimeCoreOf 5 K y.2
      have hep : IsPGroup 5 ↥(Subgroup.zpowers e) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime he5 he1, pow_one])
      have hz : ∀ v ∈ Subgroup.zpowers e, v * (y : G) * v⁻¹ * (y : G)⁻¹ ∈ O := by
        intro v hv
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
        have h1 := hbar j y
        have h2 : kb ^ j * π y * (kb ^ j)⁻¹ = π y := by
          rw [(hcomm.zpow_left j).eq]
          group
        rw [h2] at h1
        set u : ↥K := ⟨e ^ j * (y : G) * (e ^ j)⁻¹,
          (Subgroup.mem_normalizer_iff.1 (Subgroup.zpow_mem _ heN j) y).1 y.2⟩ with hu
        have h3 : u⁻¹ * y ∈ O' := QuotientGroup.eq.1 h1
        have h4 : u * y⁻¹ ∈ O' := by
          have h5 := O'.inv_mem ((GLAPPrimeCore.normal 5 ↥K).conj_mem _ h3 y)
          have e' : (y * (u⁻¹ * y) * y⁻¹)⁻¹ = u * y⁻¹ := by group
          rwa [e'] at h5
        exact (mem_gLAPPrimeCoreOf_iff 5 K _).2 ⟨(u * y⁻¹).2, h4⟩
      obtain ⟨c, hc, o, ho, hyco⟩ := Claims1110b.exists_fixed_mul hep hVX le_rfl hOcop hzX hz
      have hoK : o ∈ K := gLAPPrimeCoreOf_le 5 K ho
      have hcK : c ∈ K := by
        have : c = (y : G) * o⁻¹ := by rw [hyco]; group
        rw [this]
        exact K.mul_mem y.2 (K.inv_mem hoK)
      refine ⟨⟨c, hcK⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_centralizer_singleton_iff.2
        ((Subgroup.mem_centralizer_iff.1 hc e (Subgroup.mem_zpowers e)).symm)), ?_⟩
      obtain ⟨hoK', ho'⟩ := (mem_gLAPPrimeCoreOf_iff 5 K o).1 ho
      have hy' : y = ⟨c, hcK⟩ * ⟨o, hoK⟩ := Subtype.ext hyco
      rw [hy', map_mul, show π ⟨o, hoK⟩ = 1 from (QuotientGroup.eq_one_iff _).2 ho', mul_one]
  have hker1 : Nat.Coprime 5 (Nat.card ↥(C' ⊓ π.ker)) := by
    refine Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) ?_
    rw [hπ, QuotientGroup.ker_mk']
    exact CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 5 ↥K
  have h1 := CFSG.HardMathSupport.Solomon.Coordinator.i227m_glaPLayer_map hp π hker1
  rw [hCmap] at h1
  have hker2 : Nat.Coprime 5 (Nat.card ↥(C' ⊓ (K.subtype).ker)) := by
    rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 5
  have h2 := CFSG.HardMathSupport.Solomon.Coordinator.i227m_glaPLayer_map hp K.subtype hker2
  have hCK : C'.map K.subtype = K ⊓ Cg e := by
    rw [hC', Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [hCK] at h2
  have himg : ∀ J : Subgroup ↥K, GLAPComponent 5 C' J → J.map π = Lb := by
    intro J hJ
    have hJ' := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map hp π hker1 hJ
    rw [hCmap] at hJ'
    have hJL : J.map π ≤ Lb := le_sSup hJ'
    have hsn : IsSubnormal (J.map π) Lb := isSubnormal_of_le_of_le hJ'.2.1 hJL
      (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110b.glaPLayer_le'' 5 _)
    exact CFSG.LocalAnalysis.GLTheoremA.AltDown.eq_of_isSubnormal_of_isSimpleGroup hsn
      (glaPComponent_ne_bot' hJ')
  have hLne : GLAPLayer 5 C' ≠ ⊥ := by
    intro hb
    have : Lb = ⊥ := by rw [hLb, h1, hb, Subgroup.map_bot]
    have hc := hLc
    rw [this, Subgroup.card_bot] at hc
    norm_num at hc
  obtain ⟨J₀, hJ₀, -⟩ : ∃ J₀ : Subgroup ↥K, GLAPComponent 5 C' J₀ ∧ J₀ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hLne
    refine sSup_eq_bot.2 fun J hJ => hcon J hJ
  have huniq : ∀ J : Subgroup ↥K, GLAPComponent 5 C' J → J = J₀ := fun J hJ =>
    CFSG.LocalAnalysis.GLTheoremA.glaPComponent_eq_of_map_eq hp π hker1 hJ hJ₀
      (by rw [himg J hJ, himg J₀ hJ₀])
  have hlayer : GLAPLayer 5 C' = J₀ :=
    le_antisymm (sSup_le fun J hJ => le_of_eq (huniq J hJ)) (le_sSup hJ₀)
  have hKe : GLAPLayer 5 (K ⊓ Cg e) = J₀.map K.subtype := by rw [h2, hlayer]
  refine ⟨?_, ?_⟩
  · rw [hKe]
    have := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map hp K.subtype hker2 hJ₀
    rwa [hCK] at this
  · rw [hKe]
    have hsub : ¬ 5 ∣ Nat.card ↥(K.subtype).ker := by
      rw [Subgroup.ker_subtype, Subgroup.card_bot]
      norm_num
    have hπk : ¬ 5 ∣ Nat.card ↥π.ker := by
      rw [hπ, QuotientGroup.ker_mk']
      exact (Nat.Prime.coprime_iff_not_dvd hp).1
        (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 5 ↥K)
    obtain ⟨e₁⟩ := CFSG.LocalAnalysis.GLTheoremA.nonempty_pQuot_equiv_map hp hsub J₀
    obtain ⟨e₂⟩ := CFSG.LocalAnalysis.GLTheoremA.nonempty_pQuot_equiv_map hp hπk J₀
    rw [himg J₀ hJ₀] at e₂
    obtain ⟨e₃⟩ := CFSG.LocalAnalysis.GLTheoremA.nonempty_pQuot_equiv_of_simple hp (F := Lb)
      (by rw [hLc]; norm_num)
    exact ⟨e₁.symm.trans (e₂.trans (e₃.trans ψ))⟩

theorem ke_glaPComponent_cg2 {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 5 B M E A a K) {e : G}
    (hKe : GLAPComponent 5 (K ⊓ Cg e) (GLAPLayer 5 (K ⊓ Cg e))) :
    GLAPComponent 5 (Cg2 e a) (GLAPLayer 5 (K ⊓ Cg e)) := by
  have hsn : IsSubnormal (K ⊓ Cg e) (Cg2 e a) := by
    rw [cg2_eq_inf]
    exact h.hK.2.1.inf (Cg e)
  exact CFSG.HardMathSupport.Solomon.LocalBalance.Lemma25Ns.glaPComponent_of_isSubnormal
    (by norm_num) hsn hKe

end Ke

section IeStar

variable {G : Type} [Group G] [Finite G]

theorem gLBConj_iSup₂ {ι : Sort*} {κ : ι → Sort*} (g : G) (f : ∀ i, κ i → Subgroup G) :
    GLBConj g (⨆ i, ⨆ j, f i j) = ⨆ i, ⨆ j, GLBConj g (f i j) := by
  simp only [GLBConj, Subgroup.map_iSup]

theorem ieStarOf_eq_iSup (K : Subgroup G) {e a : G} (hae : a ∈ Cg e) {J₁ : Subgroup G}
    (hI : Claims1110b.IeOf K e = ⨆ g ∈ Subgroup.zpowers a, GLBConj g J₁) :
    Claims1110c.IeStarOf K e = ⨆ c ∈ Cg e, GLBConj c J₁ := by
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    rw [hI, gLBConj_iSup₂]
    refine iSup₂_le fun h hh => ?_
    rw [gLBConj_gLBConj]
    exact le_iSup₂_of_le (h * g) ((Cg e).mul_mem ((Subgroup.zpowers_le).2 hae hh) hg) le_rfl
  · refine iSup₂_le fun c hc => ?_
    have h1 : GLBConj c J₁ ≤ GLBConj c (Claims1110b.IeOf K e) := by
      rw [hI]
      exact gLBConj_mono c (le_iSup₂_of_le 1 (Subgroup.one_mem _) (le_of_eq (gLBConj_one J₁).symm))
    exact h1.trans (le_iSup₂_of_le (f := fun g (_ : g ∈ Cg e) => GLBConj g (Claims1110b.IeOf K e)) c hc le_rfl)

theorem glaPComponent_gLBConj_cg {p : ℕ} {e c : G} (hc : c ∈ Cg e) {J : Subgroup G}
    (hJ : GLAPComponent p (Cg e) J) : GLAPComponent p (Cg e) (GLBConj c J) := by
  have h := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hJ c
  rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hc)] at h

theorem center_gLBConj_eq_bot {p : ℕ} {J : Subgroup G} (c : G) (hZ : Subgroup.center (barOf p J) = ⊥) :
    Subgroup.center (barOf p (GLBConj c J)) = ⊥ := by
  have h := Subgroup.map_center_eq (CFSG.LocalAnalysis.GLTheoremB.conjQuotEquiv p c J)
  rw [hZ, Subgroup.map_bot] at h
  exact h.symm

theorem eq_one_of_mem_ieStar {K : Subgroup G} {e : G} {J₁ : Subgroup G}
    (hJ₁ : GLAPComponent 5 (Cg e) J₁) (hZ : Subgroup.center (barOf 5 J₁) = ⊥)
    (hI : Claims1110c.IeStarOf K e = ⨆ c ∈ Cg e, GLBConj c J₁) {x : G} (hxC : x ∈ Cg e)
    (hxI : x ∈ Claims1110c.IeStarOf K e)
    (hx : ∀ y ∈ Claims1110c.IeStarOf K e, x * y * x⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf 5 (Cg e)) {k : ℕ}
    (hk : x ^ (5 ^ k) = 1) : x = 1 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set 𝒥 : Finset (Subgroup G) :=
    (Set.toFinite {J : Subgroup G | ∃ c ∈ Cg e, J = GLBConj c J₁}).toFinset with h𝒥
  have hmem : ∀ J, J ∈ 𝒥 ↔ ∃ c ∈ Cg e, J = GLBConj c J₁ := fun J => by
    rw [h𝒥, Set.Finite.mem_toFinset]
    rfl
  have hcomp : ∀ J ∈ 𝒥, GLAPComponent 5 (Cg e) J := by
    intro J hJ
    obtain ⟨c, hc, rfl⟩ := (hmem J).1 hJ
    exact glaPComponent_gLBConj_cg hc hJ₁
  have hZ𝒥 : ∀ J ∈ 𝒥, Subgroup.center (barOf 5 J) = ⊥ := by
    intro J hJ
    obtain ⟨c, hc, rfl⟩ := (hmem J).1 hJ
    exact center_gLBConj_eq_bot c hZ
  have hle : Claims1110c.IeStarOf K e ≤ ⨆ J ∈ 𝒥, J := by
    rw [hI]
    exact iSup₂_le fun c hc => le_iSup₂_of_le (GLBConj c J₁) ((hmem _).2 ⟨c, hc, rfl⟩) le_rfl
  have hge : ∀ J ∈ 𝒥, J ≤ Claims1110c.IeStarOf K e := by
    intro J hJ
    obtain ⟨c, hc, rfl⟩ := (hmem J).1 hJ
    rw [hI]
    exact le_iSup₂_of_le c hc le_rfl
  have hxO := mem_core_of_mem_iSup (by norm_num : Nat.Prime 5) 𝒥 hcomp hZ𝒥 x
    (Subgroup.mem_sup_left (hle hxI)) (fun J hJ => ⟨hxC, fun y hy => hx y (hge J hJ hy)⟩)
  exact eq_one_of_mem_core hxO hk

end IeStar

section SylowTools

variable {G : Type} [Group G] [Finite G]

theorem isSylowIn_inf' {p : ℕ} [Fact p.Prime] {X O R : Subgroup G} (hR : IsSylowIn p X R)
    (hOX : O ≤ X) (hXO : X ≤ Subgroup.normalizer (O : Set G)) : IsSylowIn p O (R ⊓ O) := by
  refine ⟨inf_le_right, hR.2.1.to_le inf_le_left, fun R' hR'O hR'p hle => ?_⟩
  obtain ⟨x, hxX, T, hTp, hTX, hRT, hR'T⟩ :=
    exists_conj_le_pGroup' hR.1 hR.2.1 (hR'O.trans hOX) hR'p
  have hTR : T = R := hR.2.2 T hTX hTp hRT
  rw [hTR] at hR'T
  have hO : GLBConj x O = O := gLBConj_eq_of_mem_normalizer (hXO hxX)
  have h1 : GLBConj x R' ≤ R ⊓ O := by
    refine le_inf hR'T ?_
    have := gLBConj_mono x hR'O
    rwa [hO] at this
  have h2 : Nat.card ↥R' ≤ Nat.card ↥(R ⊓ O) := by
    rw [← Claims1110.card_conj x R']
    exact Subgroup.card_le_of_le h1
  exact (Subgroup.eq_of_le_of_card_ge hle h2).symm

theorem isSylowIn_of_top {p : ℕ} {X R : Subgroup G} (hR : IsSylowIn p ⊤ R) (hRX : R ≤ X) :
    IsSylowIn p X R :=
  ⟨hRX, hR.2.1, fun R' _ hR'p hle => hR.2.2 R' le_top hR'p hle⟩

theorem barX_ne_bot_of_glaPComponent {p : ℕ} {X J : Subgroup G} (hJ : GLAPComponent p X J) :
    (J.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) ≠ ⊥ := by
  intro hbot
  have h3 := hJ.2.2.1
  rw [hbot] at h3
  obtain ⟨-, hsimple⟩ := h3.2.2
  have := hsimple.toNontrivial
  have hss : Subsingleton (↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) ⧸
      Subgroup.center ↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X))) := inferInstance
  exact (not_subsingleton_iff_nontrivial.2 inferInstance) hss

theorem prime_dvd_card_of_glaPComponent {p : ℕ} (hp : p.Prime) {X J : Subgroup G}
    (hJ : GLAPComponent p X J) : p ∣ Nat.card J := by
  by_contra hnd
  have hcop : Nat.Coprime p (Nat.card J) := (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
  have htop : GLAPPrimeCore p ↥J = ⊤ := by
    have : (⊤ : Subgroup ↥J) ≤ GLAPPrimeCore p ↥J :=
      le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩
    exact top_le_iff.1 this
  have hJO : J ≤ GLAPPrimeCoreOf p X := by
    intro j hj
    refine CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal p hJ.2.1 ?_
    exact (mem_gLAPPrimeCoreOf_iff p J j).2 ⟨hj, htop ▸ Subgroup.mem_top _⟩
  apply barX_ne_bot_of_glaPComponent hJ
  rw [eq_bot_iff]
  rintro _ ⟨⟨j, hjX⟩, hj, rfl⟩
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨hjX', hj'⟩ := (mem_gLAPPrimeCoreOf_iff p X j).1 (hJO (Subgroup.mem_subgroupOf.1 hj))
  exact hj'

theorem exists_pow_eq_one_of_isPGroup {p : ℕ} {R : Subgroup G} (hR : IsPGroup p ↥R) {x : G}
    (hx : x ∈ R) : ∃ k : ℕ, x ^ (p ^ k) = 1 := by
  obtain ⟨k, hk⟩ := hR ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

end SylowTools

section Single

variable {G : Type} [Group G] [Finite G]

@[expose] def OutRankLeOne (J : Type) [Group J] : Prop :=
  ∀ X : Subgroup (MulAut J), IsPGroup 5 X →
    (∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ innerAut J) → (∀ x ∈ X, x ^ 5 ∈ innerAut J) →
    Nat.card X ≤ 5 * Nat.card ↥(X ⊓ innerAut J)

theorem iSup_conj_le_normalizer {p : ℕ} (hp : p.Prime) {e : G} {J₁ : Subgroup G}
    (hJ₁ : GLAPComponent p (Cg e) J₁) {d : G} (hd : d ∈ Cg e) :
    (⨆ c ∈ Cg e, GLBConj c J₁) ≤ Subgroup.normalizer ((GLBConj d J₁ : Subgroup G) : Set G) := by
  refine iSup₂_le fun c hc => ?_
  by_cases hcd : GLBConj c J₁ = GLBConj d J₁
  · rw [hcd]
    exact Subgroup.le_normalizer
  · have hle := Claims1110.le_centBar_of_ne' hp (glaPComponent_gLBConj_cg hd hJ₁)
      (glaPComponent_gLBConj_cg hc hJ₁) hcd
    intro x hx
    exact (Claims1110.mem_centBar_iff'.1 (hle hx)).2.1

theorem eq_one_of_mem_inf_conj {e : G} {J₁ J' : Subgroup G} (hJ₁ : GLAPComponent 5 (Cg e) J₁)
    (hJ' : GLAPComponent 5 (Cg e) J') (hne : J' ≠ J₁) (hZ : Subgroup.center (barOf 5 J₁) = ⊥)
    {x : G} (hx1 : x ∈ J₁) (hx2 : x ∈ J') {k : ℕ} (hk : x ^ (5 ^ k) = 1) : x = 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hxc := le_centMod_of_ne (by norm_num) hJ₁ hJ' hne hx2
  have hxO : x ∈ GLAPPrimeCoreOf 5 J₁ := mem_core_of_center_eq_bot hZ hx1 fun y hy =>
    core_inf_le hJ₁.1 (Subgroup.mem_inf.2 ⟨hxc.2 y hy,
      J₁.mul_mem (J₁.mul_mem (J₁.mul_mem hx1 hy) (J₁.inv_mem hx1)) (J₁.inv_mem hy)⟩)
  exact eq_one_of_mem_core (X := J₁) hxO hk

theorem conj_eq_of_isCyclic {K : Subgroup G} {e : G} {J₁ : Subgroup G}
    (hJ₁ : GLAPComponent 5 (Cg e) J₁) (hZ : Subgroup.center (barOf 5 J₁) = ⊥)
    (hI : Claims1110c.IeStarOf K e = ⨆ c ∈ Cg e, GLBConj c J₁) {R : Subgroup G}
    (hR : IsSylowIn 5 (Cg e) R) (hcyc : IsCyclic ↥(R ⊓ Claims1110c.IeStarOf K e)) :
    ∀ c ∈ Cg e, GLBConj c J₁ = J₁ := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  intro c hc
  by_contra hne
  set I := Claims1110c.IeStarOf K e with hIdef
  set J' := GLBConj c J₁ with hJ'def
  have hJ' : GLAPComponent 5 (Cg e) J' := glaPComponent_gLBConj_cg hc hJ₁
  have hW : IsSylowIn 5 I (R ⊓ I) := isSylowIn_inf' hR (Claims1110c.ieStarOf_le_cg K e)
    (Claims1110c.cg_le_normalizer_ieStarOf K e)
  have hJ₁I : J₁ ≤ I := by
    rw [hI]
    exact le_iSup₂_of_le 1 (Subgroup.one_mem _) (le_of_eq (gLBConj_one J₁).symm)
  have hJ'I : J' ≤ I := by
    rw [hI]
    exact le_iSup₂_of_le c hc le_rfl
  have hIN₁ : I ≤ Subgroup.normalizer (J₁ : Set G) := by
    have h := iSup_conj_le_normalizer hp hJ₁ (Subgroup.one_mem (Cg e))
    rwa [gLBConj_one, ← hI] at h
  have hIN' : I ≤ Subgroup.normalizer (J' : Set G) := by
    have h := iSup_conj_le_normalizer hp hJ₁ hc
    rwa [← hI] at h
  have hel : ∀ L : Subgroup G, GLAPComponent 5 (Cg e) L → L ≤ I →
      I ≤ Subgroup.normalizer (L : Set G) → ∃ x ∈ R ⊓ I ⊓ L, orderOf x = 5 := by
    intro L hL hLI hIL
    have hWL : IsSylowIn 5 L (R ⊓ I ⊓ L) := isSylowIn_inf' hW hLI hIL
    have hcard := Claims1110.card_of_isSylowIn hWL
    have hdvd : 5 ∣ Nat.card ↥(R ⊓ I ⊓ L) := by
      rw [hcard]
      have h1 : (Nat.card L).factorization 5 ≠ 0 :=
        (Nat.Prime.factorization_pos_of_dvd hp Nat.card_pos.ne' (prime_dvd_card_of_glaPComponent hp hL)).ne'
      exact dvd_pow_self 5 h1
    obtain ⟨⟨x, hx⟩, hxo⟩ := exists_prime_orderOf_dvd_card' (G := ↥(R ⊓ I ⊓ L)) 5 hdvd
    exact ⟨x, hx, by rw [← hxo, Subgroup.orderOf_mk]⟩
  obtain ⟨x₁, hx₁, hx₁o⟩ := hel J₁ hJ₁ hJ₁I hIN₁
  obtain ⟨x₂, hx₂, hx₂o⟩ := hel J' hJ' hJ'I hIN'
  have hx₁R : x₁ ∈ R := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx₁).1).1
  have hx₂R : x₂ ∈ R := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx₂).1).1
  have hx₁J : x₁ ∈ J₁ := (Subgroup.mem_inf.1 hx₁).2
  have hx₂J : x₂ ∈ J' := (Subgroup.mem_inf.1 hx₂).2
  have hx₁W : x₁ ∈ R ⊓ I := (Subgroup.mem_inf.1 hx₁).1
  have hx₂W : x₂ ∈ R ⊓ I := (Subgroup.mem_inf.1 hx₂).1
  have hx₁5 : x₁ ^ 5 = 1 := hx₁o ▸ pow_orderOf_eq_one x₁
  have hx₂5 : x₂ ^ 5 = 1 := hx₂o ▸ pow_orderOf_eq_one x₂
  have hcomm : x₂ * x₁ = x₁ * x₂ := by
    have hc := (le_centMod_of_ne hp hJ₁ hJ' hne hx₂J).2 x₁ hx₁J
    have hR' : x₂ * x₁ * x₂⁻¹ * x₁⁻¹ ∈ R :=
      R.mul_mem (R.mul_mem (R.mul_mem hx₂R hx₁R) (R.inv_mem hx₂R)) (R.inv_mem hx₁R)
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup hR.2.1 hR'
    have h1 := eq_one_of_mem_core hc hk
    calc x₂ * x₁ = (x₂ * x₁ * x₂⁻¹ * x₁⁻¹) * (x₁ * x₂) := by group
      _ = x₁ * x₂ := by rw [h1, one_mul]
  have hx₂n : x₂ ∉ Subgroup.zpowers x₁ := by
    intro hm
    have hmJ : x₂ ∈ J₁ := (Subgroup.zpowers_le.2 hx₁J) hm
    have h1 := eq_one_of_mem_inf_conj hJ₁ hJ' hne hZ hmJ hx₂J (k := 1) (by rw [pow_one]; exact hx₂5)
    rw [h1, orderOf_one] at hx₂o
    norm_num at hx₂o
  have hcard := Claims1110.card_sup_zpowers hx₂n hx₂5 (fun y hy => by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.zpow_left (show Commute x₁ x₂ from hcomm.symm) j)).eq)
  rw [Nat.card_zpowers, hx₁o] at hcard
  set T : Subgroup G := Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ with hT
  have hTW : T ≤ R ⊓ I := sup_le ((Subgroup.zpowers_le).2 hx₁W) ((Subgroup.zpowers_le).2 hx₂W)
  have hTel : IsElemAbelian 5 T := by
    have hz₁ : IsElemAbelian 5 (Subgroup.zpowers x₁) := by
      rw [Subgroup.zpowers_eq_closure]
      exact l1110_isElemAbelian_closure_singleton hx₁5
    have hz₂ : IsElemAbelian 5 (Subgroup.zpowers x₂) := by
      rw [Subgroup.zpowers_eq_closure]
      exact l1110_isElemAbelian_closure_singleton hx₂5
    refine isElemAbelian_sup_of_commute hz₁ hz₂ ?_
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.zpow_left (show Commute x₂ x₁ from hcomm) j)).eq
  set T' : Subgroup ↥(R ⊓ I) := T.subgroupOf (R ⊓ I) with hT'
  haveI : IsCyclic ↥(R ⊓ I) := hcyc
  have hT'card : Nat.card ↥T' = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTW).toEquiv
  have h5 := Claims1110b.card_le_of_isCyclic_of_pow (T := T') inferInstance (fun t ht => Subtype.ext
    (by rw [Subgroup.coe_pow, OneMemClass.coe_one]; exact hTel.2 _ (Subgroup.mem_subgroupOf.1 ht)))
  rw [hT'card, hcard] at h5
  norm_num at h5

theorem comm_mem_core_of_barAut_eq_one {p : ℕ} {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (h1 : barAut p L ⟨g, hg⟩ = 1) :
    ∀ y ∈ L, g * y * g⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf p L := by
  obtain ⟨_, _, h⟩ := (Claims1110.mem_centBar_iff_forall' (X := ⊤)).1
    (Claims1110.mem_centBar_iff'.2 ⟨trivial, hg, h1⟩)
  exact h

theorem barAut_eq_one_of_comm_mem_core {p : ℕ} {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G))
    (h : ∀ y ∈ L, g * y * g⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf p L) : barAut p L ⟨g, hg⟩ = 1 := by
  obtain ⟨-, hg', h1⟩ := Claims1110.mem_centBar_iff'.1
    ((Claims1110.mem_centBar_iff_forall' (X := ⊤)).2 ⟨trivial, hg, h⟩)
  exact h1

theorem factorization_card_barOf (p : ℕ) [Fact p.Prime] (J : Subgroup G) :
    (Nat.card (barOf p J)).factorization p = (Nat.card J).factorization p := by
  have hp : p.Prime := Fact.out
  have hJcard : Nat.card J = Nat.card (barOf p J) * Nat.card (GLAPPrimeCore p ↥J) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore p ↥J)
  rw [hJcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd
      ((hp.coprime_iff_not_dvd).1
        (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux p ↥J)), add_zero]

theorem card_le_of_single {K : Subgroup G} {e : G} {J₁ : Subgroup G}
    (hJ₁ : GLAPComponent 5 (Cg e) J₁) (hZ : Subgroup.center (barOf 5 J₁) = ⊥)
    (hIJ : Claims1110c.IeStarOf K e = J₁) (hN : Cg e ≤ Subgroup.normalizer (J₁ : Set G))
    {R : Subgroup G} (hR : IsSylowIn 5 (Cg e) R) (hOut : OutRankLeOne (barOf 5 J₁))
    {F : Subgroup G} (hFR : F ≤ R)
    (hFc : ∀ x ∈ F, ∀ y ∈ F, x * y * x⁻¹ * y⁻¹ ∈
      (R ⊓ Claims1110c.IeStarOf K e) ⊔ Claims1110c.CRIeStar R K e)
    (hF5 : ∀ x ∈ F, x ^ 5 ∈ (R ⊓ Claims1110c.IeStarOf K e) ⊔ Claims1110c.CRIeStar R K e) :
    Nat.card ↥F ≤ 5 * Nat.card ↥(F ⊓ ((R ⊓ Claims1110c.IeStarOf K e) ⊔ Claims1110c.CRIeStar R K e)) := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  set I := Claims1110c.IeStarOf K e with hIdef
  set W := R ⊓ I with hW
  set V := Claims1110c.CRIeStar R K e with hV
  have hRN : R ≤ Subgroup.normalizer (J₁ : Set G) := hR.1.trans hN
  set φ : ↥R →* MulAut (barOf 5 J₁) := (barAut 5 J₁).comp (Subgroup.inclusion hRN) with hφ
  have hφapp : ∀ (r : G) (hr : r ∈ R), φ ⟨r, hr⟩ = barAut 5 J₁ ⟨r, hRN hr⟩ := fun _ _ => rfl
  set π : ↥J₁ →* barOf 5 J₁ := QuotientGroup.mk' (GLAPPrimeCore 5 ↥J₁) with hπ
  have hconjinj : Function.Injective (MulAut.conj : barOf 5 J₁ →* MulAut (barOf 5 J₁)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    have hc : z ∈ Subgroup.center (barOf 5 J₁) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have h1 := congrArg (fun ψ : MulAut (barOf 5 J₁) => ψ w) (MonoidHom.mem_ker.1 hz)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm
    rwa [hZ] at hc
  have hWVinn : ∀ (x : G) (hx : x ∈ R), x ∈ W ⊔ V → φ ⟨x, hx⟩ ∈ innerAut (barOf 5 J₁) := by
    have hle : W ⊔ V ≤ ((innerAut (barOf 5 J₁)).comap φ).map R.subtype := by
      refine sup_le (fun w hw => ?_) (fun v hv => ?_)
      · have hwR : w ∈ R := (Subgroup.mem_inf.1 hw).1
        have hwJ : w ∈ J₁ := hIJ ▸ (Subgroup.mem_inf.1 hw).2
        refine ⟨⟨w, hwR⟩, ?_, rfl⟩
        show φ ⟨w, hwR⟩ ∈ innerAut (barOf 5 J₁)
        rw [hφapp]
        have : barAut 5 J₁ ⟨w, hRN hwR⟩ = MulAut.conj (QuotientGroup.mk (⟨w, hwJ⟩ : J₁) : barOf 5 J₁) :=
          Claims1110.barAut_of_mem hwJ
        rw [this]
        exact ⟨_, rfl⟩
      · obtain ⟨hvR, hvC, hvI⟩ := (Claims1110c.mem_cRIeStar).1 hv
        refine ⟨⟨v, hvR⟩, ?_, rfl⟩
        show φ ⟨v, hvR⟩ ∈ innerAut (barOf 5 J₁)
        have hcomm : ∀ y ∈ J₁, v * y * v⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf 5 J₁ := by
          intro y hy
          have hyI : y ∈ I := by rw [hIJ]; exact hy
          have hconjJ : v * y * v⁻¹ ∈ J₁ := (Subgroup.mem_normalizer_iff.1 (hRN hvR) y).1 hy
          exact core_inf_le hJ₁.1 (Subgroup.mem_inf.2 ⟨hvI y hyI, J₁.mul_mem hconjJ (J₁.inv_mem hy)⟩)
        rw [hφapp, barAut_eq_one_of_comm_mem_core (hRN hvR) hcomm]
        exact Subgroup.one_mem _
    intro x hx hxWV
    obtain ⟨y, hy, hyx⟩ := hle hxWV
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rw [← this]
    exact hy
  set T : Subgroup G := R ⊓ J₁ with hT
  have hTsyl : IsSylowIn 5 J₁ T := isSylowIn_inf' hR hJ₁.1 hN
  set T' : Subgroup ↥J₁ := T.subgroupOf J₁ with hT'
  set Tb : Subgroup (barOf 5 J₁) := T'.map π with hTb
  have hTinj : Function.Injective (π.comp T'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have hxR : (((x : ↥J₁) : G)) ∈ R := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 x.2)).1
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup hR.2.1 hxR
    have hxO : (((x : ↥J₁) : G)) ∈ GLAPPrimeCoreOf 5 J₁ :=
      (mem_gLAPPrimeCoreOf_iff 5 J₁ _).2 ⟨(x : ↥J₁).2, hx⟩
    have h1 := eq_one_of_mem_core hxO hk
    exact Subgroup.mem_bot.2 (Subtype.ext (Subtype.ext h1))
  have hTbcard : Nat.card ↥Tb = Nat.card ↥T := by
    have h1 : (π.comp T'.subtype).range = Tb := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1, ← Nat.card_congr (MonoidHom.ofInjective hTinj).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hTbp : IsPGroup 5 ↥Tb := (hR.2.1.to_le (inf_le_left : T ≤ R)).of_equiv
    (Subgroup.subgroupOfEquivOfLe inf_le_right).symm |>.map π
  have hTbsyl : IsSylowIn 5 ⊤ Tb := by
    refine Claims1110.isSylowIn_of_card le_top hTbp ?_
    rw [hTbcard, Claims1110.card_of_isSylowIn hTsyl, Subgroup.card_top, factorization_card_barOf]
  have hkey : ∀ (f : G) (hf : f ∈ R), φ ⟨f, hf⟩ ∈ innerAut (barOf 5 J₁) → f ∈ W ⊔ V := by
    intro f hf hfi
    set S : Subgroup (MulAut (barOf 5 J₁)) := φ.range ⊓ innerAut (barOf 5 J₁) with hS
    have hSp : IsPGroup 5 ↥S :=
      (hR.2.1.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective).to_le inf_le_left
    set S' : Subgroup (barOf 5 J₁) := S.comap (MulAut.conj : barOf 5 J₁ →* MulAut (barOf 5 J₁)) with hS'
    have hS'p : IsPGroup 5 ↥S' := hSp.comap_of_injective _ hconjinj
    have hTbS' : Tb ≤ S' := by
      rintro _ ⟨⟨t, htJ⟩, ht, rfl⟩
      have htT : t ∈ T := Subgroup.mem_subgroupOf.1 ht
      have htR : t ∈ R := (Subgroup.mem_inf.1 htT).1
      show MulAut.conj (π ⟨t, htJ⟩) ∈ S
      have heq : MulAut.conj (π ⟨t, htJ⟩) = φ ⟨t, htR⟩ := by
        rw [hφapp]
        exact (Claims1110.barAut_of_mem htJ).symm
      rw [heq]
      exact ⟨⟨_, rfl⟩, heq ▸ ⟨_, rfl⟩⟩
    have hS'eq : S' = Tb := hTbsyl.2.2 S' le_top hS'p hTbS'
    obtain ⟨q, hq⟩ := hfi
    have hqS : q ∈ S' := by
      show MulAut.conj q ∈ S
      rw [hq]
      exact ⟨⟨_, rfl⟩, ⟨q, hq⟩⟩
    rw [hS'eq] at hqS
    obtain ⟨⟨t, htJ⟩, ht, rfl⟩ := hqS
    have htT : t ∈ T := Subgroup.mem_subgroupOf.1 ht
    have htR : t ∈ R := (Subgroup.mem_inf.1 htT).1
    have htf : φ ⟨t⁻¹ * f, R.mul_mem (R.inv_mem htR) hf⟩ = 1 := by
      have e1 : (⟨t⁻¹ * f, R.mul_mem (R.inv_mem htR) hf⟩ : ↥R) = (⟨t, htR⟩ : ↥R)⁻¹ * ⟨f, hf⟩ :=
        Subtype.ext rfl
      have e2 : φ ⟨t, htR⟩ = MulAut.conj (π ⟨t, htJ⟩) := by
        rw [hφapp]
        exact Claims1110.barAut_of_mem htJ
      rw [e1, map_mul, map_inv, e2, ← hq, inv_mul_cancel]
    have hvV : t⁻¹ * f ∈ V := by
      refine (Claims1110c.mem_cRIeStar).2 ⟨R.mul_mem (R.inv_mem htR) hf,
        hR.1 (R.mul_mem (R.inv_mem htR) hf), fun y hy => ?_⟩
      have hyJ : y ∈ J₁ := by rw [← hIJ]; exact hy
      rw [hφapp] at htf
      exact CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal 5 hJ₁.2.1
        (comm_mem_core_of_barAut_eq_one _ htf y hyJ)
    have htW : t ∈ W := Subgroup.mem_inf.2 ⟨htR, by rw [hIJ]; exact htJ⟩
    have : f = t * (t⁻¹ * f) := by group
    rw [this]
    exact Subgroup.mul_mem_sup htW hvV
  set F' : Subgroup ↥R := F.subgroupOf R with hF'
  set ψ : ↥F' →* MulAut (barOf 5 J₁) := φ.comp F'.subtype with hψ
  set X : Subgroup (MulAut (barOf 5 J₁)) := ψ.range with hX
  have hXp : IsPGroup 5 ↥X := by
    have hF'p : IsPGroup 5 ↥F' := (hR.2.1.to_le hFR).of_equiv (Subgroup.subgroupOfEquivOfLe hFR).symm
    exact hF'p.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hψinn : ∀ x : ↥F', ((x : ↥R) : G) ∈ W ⊔ V → ψ x ∈ innerAut (barOf 5 J₁) :=
    fun x hx => hWVinn _ (x : ↥R).2 hx
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ innerAut (barOf 5 J₁) := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact hψinn _ (hFc _ (Subgroup.mem_subgroupOf.1 x.2) _ (Subgroup.mem_subgroupOf.1 y.2))
  have hX5 : ∀ x ∈ X, x ^ 5 ∈ innerAut (barOf 5 J₁) := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    exact hψinn _ (hF5 _ (Subgroup.mem_subgroupOf.1 x.2))
  have hOX := hOut X hXp hXc hX5
  set Y : Subgroup ↥F' := (innerAut (barOf 5 J₁)).comap ψ with hY
  have hYidx : Y.index ≤ 5 := by
    have h1 : Y.index = (innerAut (barOf 5 J₁)).relIndex X := Subgroup.index_comap _ _
    have h2 := Subgroup.index_mul_card ((innerAut (barOf 5 J₁)).subgroupOf X)
    have h3 : Nat.card ↥((innerAut (barOf 5 J₁)).subgroupOf X) = Nat.card ↥(X ⊓ innerAut (barOf 5 J₁)) := by
      rw [inf_comm, ← Subgroup.subgroupOf_map_subtype]
      exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ X.subtype_injective).toEquiv)
    rw [h3] at h2
    rw [h1, Subgroup.relIndex]
    have hpos : 0 < Nat.card ↥(X ⊓ innerAut (barOf 5 J₁)) := Nat.card_pos
    nlinarith
  have hYle : Nat.card ↥Y ≤ Nat.card ↥(F ⊓ (W ⊔ V)) := by
    refine Nat.card_le_card_of_injective (fun y => ⟨(((y : ↥F') : ↥R) : G), ?_⟩) ?_
    · refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 (y : ↥F').2, ?_⟩
      exact hkey _ ((y : ↥F') : ↥R).2 y.2
    · intro y₁ y₂ h
      have h' : (((y₁ : ↥F') : ↥R) : G) = (((y₂ : ↥F') : ↥R) : G) :=
        congrArg (fun z : ↥(F ⊓ (W ⊔ V)) => (z : G)) h
      exact Subtype.ext (Subtype.ext (Subtype.ext h'))
  have hF'c : Nat.card ↥F' = Nat.card ↥F := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFR).toEquiv
  have hcm := Subgroup.card_mul_index Y
  rw [hF'c] at hcm
  calc Nat.card ↥F = Nat.card ↥Y * Y.index := hcm.symm
    _ ≤ Nat.card ↥(F ⊓ (W ⊔ V)) * 5 := Nat.mul_le_mul hYle hYidx
    _ = 5 * Nat.card ↥(F ⊓ (W ⊔ V)) := mul_comm _ _

end Single

section Cycled

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem innerAut_normal' (Y : Type) [Group Y] : (innerAut Y).Normal := by
  constructor
  rintro _ ⟨g, rfl⟩ β
  refine ⟨β g, ?_⟩
  ext x
  simp [MulAut.conj_apply]

theorem mem_innerAut_of_pow_five {Y : Type} [Group Y] [Finite Y] (hY : IsAltType 5 Y) {φ : MulAut Y}
    (hφ : φ ^ 5 = 1) : φ ∈ innerAut Y := by
  obtain ⟨ψ⟩ := hY
  have hA : Nat.card (MulAut Y) = 120 := by
    rw [CFSG.LargeExtraspecial.S12Tri.card_mulAut_congr ψ]
    exact CFSG.GH74.GLS.LU.Local.Five.nat_card_mulAut_alternatingGroup_five
  have hYc : Nat.card Y = 60 := by
    rw [Nat.card_congr ψ.toEquiv]
    exact CFSG.GH74.GLS.LU.Local.Five.nat_card_alternatingGroup_five
  have hZ : Subgroup.center Y = ⊥ := by
    have h := Subgroup.map_center_eq ψ
    rw [alternatingGroup.center_eq_bot (by simp)] at h
    rw [eq_bot_iff]
    intro z hz
    have hz' : ψ z ∈ (Subgroup.center Y).map ψ := ⟨z, hz, rfl⟩
    rw [h, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    exact ψ.injective (by rw [hz', map_one])
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    have hc : z ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro w
      have h1 := congrArg (fun χ : MulAut Y => χ w) (MonoidHom.mem_ker.1 hz)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm
    rwa [hZ] at hc
  have hI : Nat.card (innerAut Y) = 60 := by
    rw [← hYc]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  haveI := innerAut_normal' Y
  have hidx : (innerAut Y).index = 2 := by
    have h := Subgroup.card_mul_index (innerAut Y)
    rw [hI, hA] at h
    omega
  set q := QuotientGroup.mk' (innerAut Y) φ with hq
  have hq2 : q ^ 2 = 1 := by
    have hcard : Nat.card (MulAut Y ⧸ innerAut Y) = 2 := hidx
    have := orderOf_dvd_natCard q
    rw [hcard] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  have hq5 : q ^ 5 = 1 := by rw [hq, ← map_pow, hφ, map_one]
  have hq1 : q = 1 := by
    have : q = q ^ 5 * (q ^ 2)⁻¹ * (q ^ 2)⁻¹ := by group
    rw [this, hq5, hq2]
    group
  exact (QuotientGroup.eq_one_iff φ).1 hq1

theorem exists_mem_inf_of_mem_inner {J R : Subgroup G} (hZ : Subgroup.center (barOf 5 J) = ⊥)
    (hRp : IsPGroup 5 ↥R) (hT : IsSylowIn 5 J (R ⊓ J)) {x : G} (hxR : x ∈ R)
    (hxN : x ∈ Subgroup.normalizer (J : Set G)) (hxi : barAut 5 J ⟨x, hxN⟩ ∈ innerAut (barOf 5 J)) :
    ∃ t, ∃ ht : t ∈ R ⊓ J,
      barAut 5 J ⟨x, hxN⟩ = barAut 5 J ⟨t, Subgroup.le_normalizer (Subgroup.mem_inf.1 ht).2⟩ := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  set N : Subgroup G := R ⊓ Subgroup.normalizer (J : Set G) with hNdef
  set φ : ↥N →* MulAut (barOf 5 J) := (barAut 5 J).comp (Subgroup.inclusion inf_le_right) with hφ
  have hφapp : ∀ (r : G) (hr : r ∈ N), φ ⟨r, hr⟩ = barAut 5 J ⟨r, (Subgroup.mem_inf.1 hr).2⟩ :=
    fun _ _ => rfl
  set π : ↥J →* barOf 5 J := QuotientGroup.mk' (GLAPPrimeCore 5 ↥J) with hπ
  have hconjinj : Function.Injective (MulAut.conj : barOf 5 J →* MulAut (barOf 5 J)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    have hc : z ∈ Subgroup.center (barOf 5 J) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have h1 := congrArg (fun ψ : MulAut (barOf 5 J) => ψ w) (MonoidHom.mem_ker.1 hz)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm
    rwa [hZ] at hc
  set T : Subgroup G := R ⊓ J with hTdef
  set T' : Subgroup ↥J := T.subgroupOf J with hT'
  set Tb : Subgroup (barOf 5 J) := T'.map π with hTb
  have hTinj : Function.Injective (π.comp T'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hy
    have hyR : (((y : ↥J) : G)) ∈ R := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 y.2)).1
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup hRp hyR
    have hyO : (((y : ↥J) : G)) ∈ GLAPPrimeCoreOf 5 J :=
      (mem_gLAPPrimeCoreOf_iff 5 J _).2 ⟨(y : ↥J).2, hy⟩
    have h1 := eq_one_of_mem_core hyO hk
    exact Subgroup.mem_bot.2 (Subtype.ext (Subtype.ext h1))
  have hTbcard : Nat.card ↥Tb = Nat.card ↥T := by
    have h1 : (π.comp T'.subtype).range = Tb := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1, ← Nat.card_congr (MonoidHom.ofInjective hTinj).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hTbp : IsPGroup 5 ↥Tb := (hRp.to_le (inf_le_left : T ≤ R)).of_equiv
    (Subgroup.subgroupOfEquivOfLe inf_le_right).symm |>.map π
  have hTbsyl : IsSylowIn 5 ⊤ Tb := by
    refine Claims1110.isSylowIn_of_card le_top hTbp ?_
    rw [hTbcard, Claims1110.card_of_isSylowIn hT, Subgroup.card_top, factorization_card_barOf]
  set S : Subgroup (MulAut (barOf 5 J)) := φ.range ⊓ innerAut (barOf 5 J) with hS
  have hNp : IsPGroup 5 ↥N := hRp.to_le inf_le_left
  have hSp : IsPGroup 5 ↥S :=
    (hNp.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective).to_le inf_le_left
  set S' : Subgroup (barOf 5 J) := S.comap (MulAut.conj : barOf 5 J →* MulAut (barOf 5 J)) with hS'
  have hS'p : IsPGroup 5 ↥S' := hSp.comap_of_injective _ hconjinj
  have hTbS' : Tb ≤ S' := by
    rintro _ ⟨⟨t, htJ⟩, ht, rfl⟩
    have htT : t ∈ T := Subgroup.mem_subgroupOf.1 ht
    have htN : t ∈ N := Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 htT).1, Subgroup.le_normalizer htJ⟩
    show MulAut.conj (π ⟨t, htJ⟩) ∈ S
    have heq : MulAut.conj (π ⟨t, htJ⟩) = φ ⟨t, htN⟩ := by
      rw [hφapp]
      exact (Claims1110.barAut_of_mem htJ).symm
    rw [heq]
    exact ⟨⟨_, rfl⟩, heq ▸ ⟨_, rfl⟩⟩
  have hS'eq : S' = Tb := hTbsyl.2.2 S' le_top hS'p hTbS'
  have hxN' : x ∈ N := Subgroup.mem_inf.2 ⟨hxR, hxN⟩
  obtain ⟨q, hq⟩ := hxi
  have hqS : q ∈ S' := by
    show MulAut.conj q ∈ S
    rw [hq]
    exact ⟨⟨⟨x, hxN'⟩, rfl⟩, ⟨q, hq⟩⟩
  rw [hS'eq] at hqS
  obtain ⟨⟨t, htJ⟩, ht, rfl⟩ := hqS
  have htT : t ∈ R ⊓ J := Subgroup.mem_subgroupOf.1 ht
  refine ⟨t, htT, ?_⟩
  rw [← hq]
  exact (Claims1110.barAut_of_mem htJ).symm

theorem mem_centMod_sup {p : ℕ} {X A B : Subgroup G} (hAX : A ≤ X) (hBX : B ≤ X) {c : G}
    (hA : c ∈ centMod p X A) (hB : c ∈ centMod p X B) : c ∈ centMod p X (A ⊔ B) := by
  have h1 : Subgroup.closure ({c} : Set G) ≤ centMod p X A :=
    (Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hA)
  have h2 : Subgroup.closure ({c} : Set G) ≤ centMod p X B :=
    (Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hB)
  have h3 : A ⊔ B ≤ centMod p X (Subgroup.closure ({c} : Set G)) :=
    sup_le (le_centMod_comm hAX h1) (le_centMod_comm hBX h2)
  have hcX : Subgroup.closure ({c} : Set G) ≤ X :=
    (Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hA.1)
  exact le_centMod_comm hcX h3 (Subgroup.subset_closure (Set.mem_singleton c))

theorem exists_mul_of_inner_on_each {e : G} {R : Subgroup G} (hR : IsSylowIn 5 (Cg e) R)
    (𝒥 : Finset (Subgroup G)) (h𝒥 : ∀ J ∈ 𝒥, GLAPComponent 5 (Cg e) J)
    (hZ : ∀ J ∈ 𝒥, Subgroup.center (barOf 5 J) = ⊥) (hT : ∀ J ∈ 𝒥, IsSylowIn 5 J (R ⊓ J)) :
    ∀ x ∈ R, (∀ J ∈ 𝒥, ∃ hxN : x ∈ Subgroup.normalizer (J : Set G),
        barAut 5 J ⟨x, hxN⟩ ∈ innerAut (barOf 5 J)) →
      ∃ w ∈ R ⊓ (⨆ J ∈ 𝒥, J), ∃ c ∈ R ⊓ centMod 5 (Cg e) (⨆ J ∈ 𝒥, J), x = w * c := by
  classical
  induction 𝒥 using Finset.induction_on with
  | empty =>
    intro x hxR _
    refine ⟨1, Subgroup.one_mem _, x, Subgroup.mem_inf.2 ⟨hxR, hR.1 hxR, fun y hy => ?_⟩, by group⟩
    have hy1 : y = 1 := by simpa using hy
    rw [hy1]
    simp
  | insert J 𝒥' hJ𝒥 ih =>
    intro x hxR hx
    have h𝒥' : ∀ J' ∈ 𝒥', GLAPComponent 5 (Cg e) J' := fun J' hJ' => h𝒥 J' (Finset.mem_insert_of_mem hJ')
    have hJc : GLAPComponent 5 (Cg e) J := h𝒥 J (Finset.mem_insert_self J 𝒥')
    obtain ⟨hxN, hxi⟩ := hx J (Finset.mem_insert_self J 𝒥')
    obtain ⟨t, htT, htx⟩ := exists_mem_inf_of_mem_inner (hZ J (Finset.mem_insert_self J 𝒥')) hR.2.1
      (hT J (Finset.mem_insert_self J 𝒥')) hxR hxN hxi
    have htR : t ∈ R := (Subgroup.mem_inf.1 htT).1
    have htJ : t ∈ J := (Subgroup.mem_inf.1 htT).2
    have hx'R : t⁻¹ * x ∈ R := R.mul_mem (R.inv_mem htR) hxR
    have htc : ∀ J' ∈ 𝒥', t ∈ centBar 5 (Cg e) J' := fun J' hJ' =>
      Claims1110.le_centBar_of_ne' (by norm_num) (h𝒥' J' hJ') hJc (fun h => hJ𝒥 (h ▸ hJ')) htJ
    have hx' : ∀ J' ∈ 𝒥', ∃ hxN : t⁻¹ * x ∈ Subgroup.normalizer (J' : Set G),
        barAut 5 J' ⟨t⁻¹ * x, hxN⟩ ∈ innerAut (barOf 5 J') := by
      intro J' hJ'
      obtain ⟨hxN', hxi'⟩ := hx J' (Finset.mem_insert_of_mem hJ')
      obtain ⟨-, htN', ht1⟩ := Claims1110.mem_centBar_iff'.1 (htc J' hJ')
      have hN : t⁻¹ * x ∈ Subgroup.normalizer (J' : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ htN') hxN'
      refine ⟨hN, ?_⟩
      have e1 : (⟨t⁻¹ * x, hN⟩ : ↥(Subgroup.normalizer (J' : Set G))) =
          (⟨t, htN'⟩ : ↥(Subgroup.normalizer (J' : Set G)))⁻¹ * ⟨x, hxN'⟩ := Subtype.ext rfl
      rw [e1, map_mul, map_inv, ht1, inv_one, one_mul]
      exact hxi'
    obtain ⟨w', hw', c', hc', hx'eq⟩ := ih h𝒥' (fun J' hJ' => hZ J' (Finset.mem_insert_of_mem hJ'))
      (fun J' hJ' => hT J' (Finset.mem_insert_of_mem hJ')) (t⁻¹ * x) hx'R hx'
    have hx'J : t⁻¹ * x ∈ centMod 5 (Cg e) J := by
      have hN : t⁻¹ * x ∈ Subgroup.normalizer (J : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer htJ)) hxN
      have h1 : barAut 5 J ⟨t⁻¹ * x, hN⟩ = 1 := by
        have e1 : (⟨t⁻¹ * x, hN⟩ : ↥(Subgroup.normalizer (J : Set G))) =
            (⟨t, Subgroup.le_normalizer htJ⟩ : ↥(Subgroup.normalizer (J : Set G)))⁻¹ * ⟨x, hxN⟩ :=
          Subtype.ext rfl
        rw [e1, map_mul, map_inv, htx, inv_mul_cancel]
      refine ⟨hR.1 hx'R, fun y hy => ?_⟩
      exact CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal 5 hJc.2.1
        (comm_mem_core_of_barAut_eq_one hN h1 y hy)
    have hN'X : (⨆ J' ∈ 𝒥', J') ≤ Cg e := iSup₂_le fun J' hJ' => (h𝒥' J' hJ').1
    have hw'J : w' ∈ centMod 5 (Cg e) J := by
      have hle : (⨆ J' ∈ 𝒥', J') ≤ centMod 5 (Cg e) J := iSup₂_le fun J' hJ' =>
        le_centMod_of_ne (by norm_num) hJc (h𝒥' J' hJ') (fun h => hJ𝒥 (h ▸ hJ'))
      exact hle (Subgroup.mem_inf.1 hw').2
    have hc'J : c' ∈ centMod 5 (Cg e) J := by
      have : c' = w'⁻¹ * (t⁻¹ * x) := by rw [hx'eq]; group
      rw [this]
      exact (centMod 5 (Cg e) J).mul_mem ((centMod 5 (Cg e) J).inv_mem hw'J) hx'J
    have hc'all : c' ∈ centMod 5 (Cg e) (J ⊔ ⨆ J' ∈ 𝒥', J') :=
      mem_centMod_sup hJc.1 hN'X hc'J (Subgroup.mem_inf.1 hc').2
    refine ⟨t * w', ?_, c', ?_, ?_⟩
    · rw [Finset.iSup_insert]
      exact Subgroup.mem_inf.2 ⟨R.mul_mem htR (Subgroup.mem_inf.1 hw').1,
        Subgroup.mul_mem _ (Subgroup.mem_sup_left htJ) (Subgroup.mem_sup_right (Subgroup.mem_inf.1 hw').2)⟩
    · rw [Finset.iSup_insert]
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hc').1, hc'all⟩
    · rw [mul_assoc, ← hx'eq]
      group

abbrev conjActComp (X : Subgroup G) (𝒮 : Set (Subgroup G))
    (h𝒮 : ∀ x ∈ X, ∀ J ∈ 𝒮, GLBConj x⁻¹ J ∈ 𝒮) : MulAction ↥X ↥𝒮 where
  smul x J := ⟨GLBConj (x : G)⁻¹ J, h𝒮 x x.2 J J.2⟩
  one_smul J := Subtype.ext (by
    show GLBConj ((1 : ↥X) : G)⁻¹ (J : Subgroup G) = J
    rw [OneMemClass.coe_one, inv_one, gLBConj_one])
  mul_smul x y J := Subtype.ext (by
    show GLBConj ((x * y : ↥X) : G)⁻¹ (J : Subgroup G) =
      GLBConj (x : G)⁻¹ (GLBConj (y : G)⁻¹ (J : Subgroup G))
    rw [gLBConj_gLBConj, Subgroup.coe_mul, mul_inv_rev])

theorem card_range_le_of_isPGroup {p : ℕ} [hp : Fact p.Prime] {α X : Type*} [Finite α] [Group X]
    [Finite X] (hX : IsPGroup p X) (ρ : X →* Equiv.Perm α) (hα : Nat.card α ≤ p) :
    Nat.card ρ.range ≤ p := by
  have hrp : IsPGroup p ρ.range := hX.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := hrp.exists_card_eq
  have hdvd : p ^ k ∣ (Nat.card α).factorial := by
    rw [← hk, ← Nat.card_perm]
    exact Subgroup.card_subgroup_dvd_card _
  have hdvd' : p ^ k ∣ p.factorial := hdvd.trans (Nat.factorial_dvd_factorial hα)
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have h2 : p ^ 2 ∣ p.factorial := (pow_dvd_pow p (by omega)).trans hdvd'
    have h3 : p.factorial = p * (p - 1).factorial := (Nat.mul_factorial_pred hp.out.ne_zero).symm
    rw [h3, pow_two] at h2
    have h4 : p ∣ (p - 1).factorial := Nat.dvd_of_mul_dvd_mul_left hp.out.pos h2
    rw [hp.out.dvd_factorial] at h4
    have := hp.out.two_le
    omega
  rw [hk]
  calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.out.pos hk1
    _ = p := pow_one p

theorem card_le_of_cycled {K : Subgroup G} {e a : G} {J₁ : Subgroup G}
    (hJ₁ : GLAPComponent 5 (Cg e) J₁) (hae : a ∈ Cg e) (ha5 : a ^ 5 = 1)
    (hA5 : IsAltType 5 (barOf 5 J₁))
    (hIa : Claims1110c.IeStarOf K e = ⨆ g ∈ Subgroup.zpowers a, GLBConj g J₁)
    (hconj : ∀ c ∈ Cg e, ∃ g ∈ Subgroup.zpowers a, GLBConj c J₁ = GLBConj g J₁)
    {R : Subgroup G} (hR : IsSylowIn 5 (Cg e) R) {X : Subgroup G} (hXR : X ≤ R) :
    Nat.card ↥X ≤ 5 * Nat.card ↥((R ⊓ Claims1110c.IeStarOf K e) ⊔ Claims1110c.CRIeStar R K e) := by
  classical
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  set I := Claims1110c.IeStarOf K e with hIdef
  set W := R ⊓ I with hW
  set V := Claims1110c.CRIeStar R K e with hV
  have hza : Subgroup.zpowers a ≤ Cg e := (Subgroup.zpowers_le).2 hae
  have hIc : I = ⨆ c ∈ Cg e, GLBConj c J₁ := by
    apply le_antisymm
    · rw [hIa]
      exact iSup₂_le fun g hg => le_iSup₂_of_le g (hza hg) le_rfl
    · refine iSup₂_le fun c hc => ?_
      obtain ⟨g, hg, hcg⟩ := hconj c hc
      rw [hcg, hIa]
      exact le_iSup₂_of_le g hg le_rfl
  set 𝒮 : Set (Subgroup G) := {J | ∃ g ∈ Subgroup.zpowers a, J = GLBConj g J₁} with h𝒮
  have h𝒮fin : 𝒮.Finite := Set.toFinite 𝒮
  set 𝒥 : Finset (Subgroup G) := h𝒮fin.toFinset with h𝒥
  have hmem : ∀ J, J ∈ 𝒥 ↔ ∃ g ∈ Subgroup.zpowers a, J = GLBConj g J₁ := fun J => by
    rw [h𝒥, Set.Finite.mem_toFinset]
    rfl
  have hcard𝒮 : Nat.card ↥𝒮 ≤ 5 := by
    have hsurj : Function.Surjective (fun g : ↥(Subgroup.zpowers a) =>
        (⟨GLBConj (g : G) J₁, ⟨g, g.2, rfl⟩⟩ : ↥𝒮)) := by
      rintro ⟨J, g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
    calc Nat.card ↥𝒮 ≤ Nat.card ↥(Subgroup.zpowers a) := Nat.card_le_card_of_surjective _ hsurj
      _ = orderOf a := Nat.card_zpowers a
      _ ≤ 5 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ha5)
  have hIJ : I = ⨆ J ∈ 𝒥, J := by
    rw [hIa]
    apply le_antisymm
    · exact iSup₂_le fun g hg => le_iSup₂_of_le (GLBConj g J₁) ((hmem _).2 ⟨g, hg, rfl⟩) le_rfl
    · refine iSup₂_le fun J hJ => ?_
      obtain ⟨g, hg, rfl⟩ := (hmem J).1 hJ
      exact le_iSup₂_of_le g hg le_rfl
  have hcomp : ∀ J ∈ 𝒥, GLAPComponent 5 (Cg e) J := by
    intro J hJ
    obtain ⟨g, hg, rfl⟩ := (hmem J).1 hJ
    exact glaPComponent_gLBConj_cg (hza hg) hJ₁
  have hZ₁ : Subgroup.center (barOf 5 J₁) = ⊥ := by
    obtain ⟨ψ⟩ := hA5
    have h := Subgroup.map_center_eq ψ
    rw [alternatingGroup.center_eq_bot (by simp)] at h
    rw [eq_bot_iff]
    intro z hz
    have hz' : ψ z ∈ (Subgroup.center (barOf 5 J₁)).map ψ := ⟨z, hz, rfl⟩
    rw [h, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    exact ψ.injective (by rw [hz', map_one])
  have hZ : ∀ J ∈ 𝒥, Subgroup.center (barOf 5 J) = ⊥ := by
    intro J hJ
    obtain ⟨g, hg, rfl⟩ := (hmem J).1 hJ
    exact center_gLBConj_eq_bot g hZ₁
  have hA5𝒥 : ∀ J ∈ 𝒥, IsAltType 5 (barOf 5 J) := by
    intro J hJ
    obtain ⟨g, hg, rfl⟩ := (hmem J).1 hJ
    obtain ⟨ψ⟩ := hA5
    exact ⟨(CFSG.LocalAnalysis.GLTheoremB.conjQuotEquiv 5 g J₁).symm.trans ψ⟩
  have hWsyl : IsSylowIn 5 I W := isSylowIn_inf' hR (Claims1110c.ieStarOf_le_cg K e)
    (Claims1110c.cg_le_normalizer_ieStarOf K e)
  have hT : ∀ J ∈ 𝒥, IsSylowIn 5 J (R ⊓ J) := by
    intro J hJ
    obtain ⟨g, hg, rfl⟩ := (hmem J).1 hJ
    have hJI : GLBConj g J₁ ≤ I := by rw [hIa]; exact le_iSup₂_of_le g hg le_rfl
    have hIN : I ≤ Subgroup.normalizer ((GLBConj g J₁ : Subgroup G) : Set G) := by
      rw [hIc]
      exact iSup_conj_le_normalizer hp hJ₁ (hza hg)
    have h := isSylowIn_inf' hWsyl hJI hIN
    have heq : W ⊓ GLBConj g J₁ = R ⊓ GLBConj g J₁ := by
      rw [hW, inf_assoc, inf_eq_right.2 hJI]
    rwa [heq] at h
  have h𝒮cl : ∀ x ∈ X, ∀ J ∈ 𝒮, GLBConj x⁻¹ J ∈ 𝒮 := by
    rintro x hx _ ⟨g, hg, rfl⟩
    rw [gLBConj_gLBConj]
    have hgx : g * x⁻¹ ∈ Cg e := (Cg e).mul_mem (hza hg) ((Cg e).inv_mem (hR.1 (hXR hx)))
    obtain ⟨g', hg', hgg'⟩ := hconj _ hgx
    exact ⟨g', hg', hgg'⟩
  letI := conjActComp X 𝒮 h𝒮cl
  set ρ := MulAction.toPermHom ↥X ↥𝒮 with hρ
  have hXp : IsPGroup 5 ↥X := hR.2.1.to_le hXR
  have hρc : Nat.card ρ.range ≤ 5 := card_range_le_of_isPGroup hXp ρ hcard𝒮
  have hker : ∀ x : ↥X, x ∈ ρ.ker → (x : G) ∈ W ⊔ V := by
    intro x hx
    have hfix : ∀ J ∈ 𝒮, GLBConj (x : G)⁻¹ J = J := by
      intro J hJ
      have h1 := congrArg (fun σ : Equiv.Perm ↥𝒮 => ((σ ⟨J, hJ⟩ : ↥𝒮) : Subgroup G))
        (MonoidHom.mem_ker.1 hx)
      exact h1
    have hxR : (x : G) ∈ R := hXR x.2
    have hinn : ∀ J ∈ 𝒥, ∃ hxN : (x : G) ∈ Subgroup.normalizer (J : Set G),
        barAut 5 J ⟨x, hxN⟩ ∈ innerAut (barOf 5 J) := by
      intro J hJ
      have hJ𝒮 : J ∈ 𝒮 := (hmem J).1 hJ
      have hxN : (x : G) ∈ Subgroup.normalizer (J : Set G) := by
        have h1 : (x : G)⁻¹ ∈ Subgroup.normalizer (J : Set G) :=
          mem_normalizer_iff_gLBConj_eq.2 (hfix J hJ𝒮)
        simpa using Subgroup.inv_mem _ h1
      refine ⟨hxN, mem_innerAut_of_pow_five (hA5𝒥 J hJ) ?_⟩
      obtain ⟨k, hk⟩ := exists_pow_eq_one_of_isPGroup hR.2.1 hxR
      have hk' : barAut 5 J ⟨x, hxN⟩ ^ (5 ^ k) = 1 := by
        rw [← map_pow]
        have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (J : Set G))) ^ (5 ^ k) = 1 :=
          Subtype.ext (by simpa using hk)
        rw [this, map_one]
      obtain ⟨ψ⟩ := hA5𝒥 J hJ
      have hA : Nat.card (MulAut (barOf 5 J)) = 120 := by
        rw [CFSG.LargeExtraspecial.S12Tri.card_mulAut_congr ψ]
        exact CFSG.GH74.GLS.LU.Local.Five.nat_card_mulAut_alternatingGroup_five
      have hd1 : orderOf (barAut 5 J ⟨x, hxN⟩) ∣ 5 ^ k := orderOf_dvd_of_pow_eq_one hk'
      have hd2 : orderOf (barAut 5 J ⟨x, hxN⟩) ∣ 120 := hA ▸ orderOf_dvd_natCard _
      have hd : orderOf (barAut 5 J ⟨x, hxN⟩) ∣ 5 := by
        obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hp).1 hd1
        rw [hjeq] at hd2 ⊢
        have hj1 : j ≤ 1 := by
          by_contra hj1
          have : 5 ^ 2 ∣ 120 := (pow_dvd_pow 5 (by omega)).trans hd2
          norm_num at this
        calc 5 ^ j ∣ 5 ^ 1 := pow_dvd_pow 5 hj1
          _ = 5 := pow_one 5
      exact orderOf_dvd_iff_pow_eq_one.1 hd
    obtain ⟨w, hw, c, hc, hxwc⟩ := exists_mul_of_inner_on_each hR 𝒥 hcomp hZ hT x hxR hinn
    rw [hxwc]
    refine Subgroup.mul_mem_sup ?_ ?_
    · rw [hW, hIJ]
      exact hw
    · have hcR := (Subgroup.mem_inf.1 hc).1
      have hc2 := (Subgroup.mem_inf.1 hc).2
      refine (Claims1110c.mem_cRIeStar).2 ⟨hcR, hc2.1, fun y hy => hc2.2 y ?_⟩
      rw [← hIJ]
      exact hy
  have hcardX : Nat.card ↥X = Nat.card ρ.range * Nat.card ρ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
  have hkerle : Nat.card ρ.ker ≤ Nat.card ↥(W ⊔ V) := by
    refine Nat.card_le_card_of_injective (fun x => ⟨((x : ↥X) : G), hker x x.2⟩) ?_
    intro x₁ x₂ h
    have h' : ((x₁ : ↥X) : G) = ((x₂ : ↥X) : G) := congrArg (fun z : ↥(W ⊔ V) => (z : G)) h
    exact Subtype.ext (Subtype.ext h')
  rw [hcardX]
  exact Nat.mul_le_mul hρc hkerle

end Cycled

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110d
