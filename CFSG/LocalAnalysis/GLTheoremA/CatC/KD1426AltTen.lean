module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426AltTenLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426AltTenPerm
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426AltTenTK
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426AltTenJ
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltZ
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Simple

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement
open CFSG.LocalAnalysis.GLTheoremA.KD1426Common

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426AltTen

variable {Y : Type} [Group Y] [Finite Y]

theorem center_bot_of_ten {K : Subgroup Y} (hq : CFSG.Open.IsQuasisimple ↥K)
    (hcore : GLAPPrimeCore 3 ↥K = ⊥)
    (eK : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin 10)) :
    Subgroup.center ↥K = ⊥ := by
  rcases KD264Z.center_eq_bot_or_three Nat.prime_three (by norm_num) hq hcore (by norm_num) eK with h | h
  · exact h
  · exact absurd h.2 (by norm_num)

theorem inf_centralizer_sup {K B0 : Subgroup Y} {a : Y}
    (hB0C : ∀ b ∈ B0, b ∈ Subgroup.centralizer (K : Set Y)) :
    K ⊓ Subgroup.centralizer ((Subgroup.zpowers a ⊔ B0 : Subgroup Y) : Set Y) =
      K ⊓ Subgroup.centralizer ({a} : Set Y) := by
  ext k
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hkK, hk⟩
    refine ⟨hkK, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hk ⊢
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hk h (Subgroup.mem_sup_left (Subgroup.mem_zpowers h))
  · rintro ⟨hkK, hk⟩
    refine ⟨hkK, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hk ⊢
    intro h hh
    rw [Subgroup.sup_eq_closure] at hh
    have hak : a * k = k * a := hk a (Set.mem_singleton a)
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        have hc : Commute a k := hak
        exact (hc.zpow_left n).eq
      · exact ((Subgroup.mem_centralizer_iff.1 (hB0C x hx) k hkK)).symm
    | one => simp
    | mul x y _ _ hx hy =>
      rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
    | inv x _ hx =>
      calc x⁻¹ * k = x⁻¹ * (k * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * k) * x⁻¹ := by rw [hx]
        _ = k * x⁻¹ := by group

theorem comm_zpowers {Y' : Type} [Group Y'] {a b : Y'} (h : a * b = b * a) {g : Y'}
    (hg : g ∈ Subgroup.zpowers a) : b * g = g * b := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  exact Commute.zpow_right (show Commute b a from h.symm) n

theorem card_sup_zpowers {a : Y} {B0 : Subgroup Y} (hza : Nat.card (Subgroup.zpowers a) = 3)
    (hnorm0 : B0 ≤ Subgroup.normalizer (Subgroup.zpowers a : Set Y))
    (hBz : Nat.card ↥(Subgroup.zpowers a ⊓ B0) = 1) :
    Nat.card ↥(Subgroup.zpowers a ⊔ B0) = 3 * Nat.card ↥B0 := by
  have hcard := card_sup_mul_card_inf_of_le_normalizer (A := Subgroup.zpowers a) (B := B0) hnorm0
  rw [hBz, mul_one, hza] at hcard
  exact hcard

theorem layer_sup {K B0 : Subgroup Y} (hK : K.Normal) (π : ↥K ≃* alternatingGroup (Fin 10))
    (a : Y) (σ : alternatingGroup (Fin 10)) (hσ3 : σ ^ 3 = 1)
    (hσc : ((σ : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)).support.card = 3)
    (hcomm : ∀ k : ↥K, π (KD264Inner.conjKequiv K hK a k) = σ * π k * σ⁻¹)
    (hB0C : ∀ b ∈ B0, b ∈ Subgroup.centralizer (K : Set Y)) :
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ((Subgroup.zpowers a ⊔ B0 : Subgroup Y) : Set Y))
        (((altFix (σ : Equiv.Perm (Fin 10))).comap π.toMonoidHom).map K.subtype) ∧
      GLAPLayer 3 (K ⊓ Subgroup.centralizer ((Subgroup.zpowers a ⊔ B0 : Subgroup Y) : Set Y)) =
        ((altFix (σ : Equiv.Perm (Fin 10))).comap π.toMonoidHom).map K.subtype := by
  rw [inf_centralizer_sup hB0C]
  exact KD1426AltTenLayer.layer_three_cycle hK π a σ hσ3 hσc hcomm

theorem criterion_sup {K B : Subgroup Y} (hK : K.Normal) (hB : CFSG.Open.IsElemAbelian 3 B)
    (π : ↥K ≃* alternatingGroup (Fin 10)) (ψ : ↥B →* alternatingGroup (Fin 10))
    (hψequiv : ∀ (b : ↥B) (k : ↥K),
      π (KD264Inner.conjKequiv K hK (b : Y) k) = ψ b * π k * (ψ b)⁻¹)
    (hψker : ∀ b : ↥B, ψ b = 1 ↔ (b : Y) ∈ Subgroup.centralizer (K : Set Y))
    (a : ↥B) (hσ3 : ψ a ^ 3 = 1)
    (hσc : ((ψ a : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)).support.card = 3)
    {J : Subgroup Y}
    (hJdef : J = ((altFix ((ψ a : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10))).comap
      π.toMonoidHom).map K.subtype)
    (hJK : J ≤ K) (hJa : ∀ j ∈ J, (a : Y) * j = j * (a : Y)) :
    ∀ b ∈ B, b ∈ Subgroup.centralizer (J : Set Y) ↔
      b ∈ Subgroup.zpowers (a : Y) ⊔ (B ⊓ Subgroup.centralizer (K : Set Y)) := by
  classical
  intro b hb
  constructor
  · intro hbC
    have hfix : ∀ f : alternatingGroup (Fin 10),
        f ∈ altFix ((ψ a : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)) →
          ψ ⟨b, hb⟩ * f = f * ψ ⟨b, hb⟩ := by
      intro f hf
      have hjJ : ((π.symm f : K) : Y) ∈ J := by
        rw [hJdef]
        exact Subgroup.mem_map.2 ⟨π.symm f, Subgroup.mem_comap.2 (by simpa using hf), rfl⟩
      have h1 : ((π.symm f : K) : Y) * b = b * ((π.symm f : K) : Y) :=
        Subgroup.mem_centralizer_iff.1 hbC _ hjJ
      have h2 : KD264Inner.conjKequiv K hK b (π.symm f) = π.symm f := by
        apply Subtype.ext
        rw [KD264Inner.conjKequiv_apply, ← h1, mul_inv_cancel_right]
      have h3 : π (KD264Inner.conjKequiv K hK b (π.symm f)) =
          ψ ⟨b, hb⟩ * π (π.symm f) * (ψ ⟨b, hb⟩)⁻¹ := hψequiv ⟨b, hb⟩ (π.symm f)
      rw [h2, MulEquiv.apply_symm_apply] at h3
      calc ψ ⟨b, hb⟩ * f = (ψ ⟨b, hb⟩ * f * (ψ ⟨b, hb⟩)⁻¹) * ψ ⟨b, hb⟩ := by group
        _ = f * ψ ⟨b, hb⟩ := by rw [← h3]
    have hfixP : ∀ f : Equiv.Perm (Fin 10), Equiv.Perm.sign f = 1 →
        (∀ t ∈ ((ψ a : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)).support, f t = t) →
        ((ψ ⟨b, hb⟩ : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)) * f =
          f * ((ψ ⟨b, hb⟩ : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)) := by
      intro f hf hft
      have hfA : f ∈ alternatingGroup (Fin 10) := Equiv.Perm.mem_alternatingGroup.2 hf
      have hmem : (⟨f, hfA⟩ : alternatingGroup (Fin 10)) ∈
          altFix ((ψ a : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)) :=
        mem_altFix_iff.2 (fun u hu => hft u hu)
      have h4 := congrArg (fun g : alternatingGroup (Fin 10) => (g : Equiv.Perm (Fin 10)))
        (hfix _ hmem)
      simpa using h4
    have hσP3 : ((ψ a : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, hσ3]
      rfl
    obtain ⟨i, -, hxi⟩ := KD1426AltTenPerm.fix_comm_pow hσP3 hσc
      (Equiv.Perm.mem_alternatingGroup.1 (ψ a).2) (Equiv.Perm.mem_alternatingGroup.1 (ψ ⟨b, hb⟩).2)
      hfixP
    have hxpow : ψ ⟨b, hb⟩ = ψ (a ^ i) := by
      rw [map_pow]
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      exact hxi
    have hpsic : ψ ((a ^ i)⁻¹ * ⟨b, hb⟩) = 1 := by
      rw [map_mul, map_inv, ← hxpow, inv_mul_cancel]
    have hc' : (((a ^ i)⁻¹ * ⟨b, hb⟩ : ↥B) : Y) ∈ Subgroup.centralizer (K : Set Y) :=
      (hψker _).1 hpsic
    have hcB : (((a ^ i)⁻¹ * ⟨b, hb⟩ : ↥B) : Y) ∈ B := ((a ^ i)⁻¹ * ⟨b, hb⟩ : ↥B).2
    have hbeq : b = (a : Y) ^ i * (((a ^ i)⁻¹ * ⟨b, hb⟩ : ↥B) : Y) := by
      simp
    have key : (a : Y) ^ i * (((a ^ i)⁻¹ * ⟨b, hb⟩ : ↥B) : Y) ∈
        Subgroup.zpowers (a : Y) ⊔ (B ⊓ Subgroup.centralizer (K : Set Y)) :=
      mul_mem (Subgroup.mem_sup_left (pow_mem (Subgroup.mem_zpowers (a : Y)) i))
        (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hcB, hc'⟩))
    rwa [← hbeq] at key
  · intro hbA
    have hle : Subgroup.zpowers (a : Y) ⊔ (B ⊓ Subgroup.centralizer (K : Set Y)) ≤
        Subgroup.centralizer (J : Set Y) := by
      apply sup_le
      · apply Subgroup.zpowers_le.2
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        exact (hJa j hj).symm
      · intro c hc
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 j (hJK hj)
    exact hle hbA

theorem alt10_main {K B : Subgroup Y} (hK : K.Normal) (hB : CFSG.Open.IsElemAbelian 3 B)
    (hcardB : Nat.card B = 3 ^ 4) (π : ↥K ≃* alternatingGroup (Fin 10))
    (ψ : ↥B →* alternatingGroup (Fin 10))
    (hψequiv : ∀ (b : ↥B) (k : ↥K),
      π (KD264Inner.conjKequiv K hK (b : Y) k) = ψ b * π k * (ψ b)⁻¹)
    (hψker : ∀ b : ↥B, ψ b = 1 ↔ (b : Y) ∈ Subgroup.centralizer (K : Set Y))
    (hB0c : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = 3)
    (hPc : Nat.card ψ.range = 27)
    (a : ↥B) (ha : ((ψ a : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)).support.card = 3) :
    Nat.card B = 3 ^ 4 ∧ ∃ A T : Subgroup Y, A ≤ B ∧ CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 9 ∧
      GLAPComponent 3 (K ⊓ Subgroup.centralizer (A : Set Y))
        (GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y))) ∧
      catalogIs (PSimple 3 (GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y)))) k3NoA10 ∧
      (∀ b ∈ B, b ∈ Subgroup.centralizer
          ((GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y)) : Subgroup Y) : Set Y) ↔ b ∈ A) ∧
      T ≤ GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y)) ∧ CFSG.Open.IsElemAbelian 2 T ∧
      Nat.card T = 4 ∧ B ≤ Subgroup.normalizer (T : Set Y) ∧ ⁅B, T⁆ = T ∧
      GLAPPrimeCore 3 ↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y))) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB3 : ∀ b ∈ B, b ^ 3 = 1 := hB.2
  have ha3' : (a : Y) ^ 3 = 1 := hB3 (a : Y) a.2
  have hσ3 : ψ a ^ 3 = 1 := by
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (hB3 (a : Y) a.2)
    rw [this, map_one]
  have hσ1 : ψ a ≠ 1 := by
    intro h
    rw [h] at ha
    simp at ha
  have ha1 : (a : Y) ≠ 1 := by
    intro h
    apply hσ1
    have : a = 1 := Subtype.ext h
    rw [this, map_one]
  have hza : Nat.card (Subgroup.zpowers (a : Y)) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha3' ha1
  have hcomm_ab : ∀ b ∈ B, (a : Y) * b = b * (a : Y) := fun b hb => by
    have := hB.1.is_comm.comm (⟨(a : Y), a.2⟩ : ↥B) ⟨b, hb⟩
    exact congrArg Subtype.val this
  set B0 : Subgroup Y := B ⊓ Subgroup.centralizer (K : Set Y) with hB0def
  have hB0C : ∀ b ∈ B0, b ∈ Subgroup.centralizer (K : Set Y) :=
    fun b hb => (Subgroup.mem_inf.1 hb).2
  have hnorm0 : B0 ≤ Subgroup.normalizer (Subgroup.zpowers (a : Y) : Set Y) := by
    intro b hb
    have hbB : b ∈ B := (Subgroup.mem_inf.1 hb).1
    have hab : (a : Y) * b = b * (a : Y) := hcomm_ab b hbB
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have e : b * h * b⁻¹ = h := by
        calc b * h * b⁻¹ = (b * h) * b⁻¹ := rfl
          _ = (h * b) * b⁻¹ := by rw [← comm_zpowers hab hh]
          _ = h := by group
      rw [e]
      exact hh
    · intro hg
      have hc := comm_zpowers hab hg
      have e2 : h = b⁻¹ * (b * h * b⁻¹) * b := by group
      have hinv : b⁻¹ * (b * h * b⁻¹) * b = b * h * b⁻¹ := by
        calc b⁻¹ * (b * h * b⁻¹) * b = b⁻¹ * ((b * h * b⁻¹) * b) := by group
          _ = b⁻¹ * (b * (b * h * b⁻¹)) := by rw [hc]
          _ = b * h * b⁻¹ := by group
      rw [e2, hinv]
      exact hg
  have hBz : Nat.card ↥(Subgroup.zpowers (a : Y) ⊓ B0) = 1 := by
    have hd : Nat.card ↥(Subgroup.zpowers (a : Y) ⊓ B0) ∣ 3 := by
      rw [← hza]
      exact Subgroup.card_dvd_of_le
        (inf_le_left : Subgroup.zpowers (a : Y) ⊓ B0 ≤ Subgroup.zpowers (a : Y))
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
    · exact h1
    · exfalso
      have hle : Subgroup.zpowers (a : Y) ≤ B0 := by
        have := Subgroup.eq_of_le_of_card_ge
          (inf_le_left : Subgroup.zpowers (a : Y) ⊓ B0 ≤ Subgroup.zpowers (a : Y))
          (by rw [h3, hza])
        rw [← this]
        exact inf_le_right
      have haB0 : (a : Y) ∈ B0 := hle (Subgroup.mem_zpowers _)
      apply hσ1
      exact (hψker a).2 (Subgroup.mem_inf.1 haB0).2
  have hAcard : Nat.card ↥(Subgroup.zpowers (a : Y) ⊔ B0) = 9 := by
    rw [card_sup_zpowers hza hnorm0 hBz, hB0c]
  have hcomm : ∀ k : ↥K, π (KD264Inner.conjKequiv K hK (a : Y) k) = ψ a * π k * (ψ a)⁻¹ :=
    fun k => hψequiv a k
  obtain ⟨hcompJ, hlayJ⟩ := layer_sup hK π (a : Y) (ψ a) hσ3 ha hcomm hB0C
  obtain ⟨J, hJ⟩ : ∃ J : Subgroup Y,
      J = ((altFix ((ψ a : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10))).comap
        π.toMonoidHom).map K.subtype := ⟨_, rfl⟩
  rw [← hJ] at hcompJ hlayJ
  obtain ⟨hJpc, ⟨eJ⟩, -⟩ := KD1426AltTenJ.J_pSimple π ha hJ
  have hJle : J ≤ K ⊓ Subgroup.centralizer ((Subgroup.zpowers (a : Y) ⊔ B0 : Subgroup Y) : Set Y) := by
    rw [← hlayJ]
    exact glaPLayer_le (K ⊓ Subgroup.centralizer ((Subgroup.zpowers (a : Y) ⊔ B0 : Subgroup Y) : Set Y))
  have hJK : J ≤ K := hJle.trans inf_le_left
  have hJa : ∀ j ∈ J, (a : Y) * j = j * (a : Y) := by
    intro j hj
    have hjC := (Subgroup.mem_inf.1 (hJle hj)).2
    have haA : (a : Y) ∈ ((Subgroup.zpowers (a : Y) ⊔ B0 : Subgroup Y) : Set Y) :=
      Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    exact Subgroup.mem_centralizer_iff.1 hjC (a : Y) haA
  have hcrit := criterion_sup hK hB π ψ hψequiv hψker a hσ3 ha hJ hJK hJa
  obtain ⟨TY, hTYc, hTYel, hTYle0, hBnorm, hcommT⟩ :=
    KD1426AltTenTK.lift_T hK hB π ψ hψequiv hσ3 ha (MonoidHom.mem_range.2 ⟨a, rfl⟩) hPc
  rw [← hJ] at hTYle0
  have hAB : Subgroup.zpowers (a : Y) ⊔ B0 ≤ B :=
    sup_le (Subgroup.zpowers_le.2 a.2) inf_le_left
  have hAel : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers (a : Y) ⊔ B0) :=
    isElemAbelian_of_le hAB hB
  refine ⟨hcardB, Subgroup.zpowers (a : Y) ⊔ B0, TY, hAB, hAel, hAcard, ?_, ?_, ?_, ?_,
    hTYel, hTYc, hBnorm, hcommT, ?_⟩
  · rw [hlayJ]
    exact hcompJ
  · rw [hlayJ]
    have h57 : 5 ≤ 7 := by norm_num
    exact ⟨TauCeti.CFSGIndex.alternating 7 h57, rfl, pSimple_mulEquiv hJpc eJ⟩
  · rw [hlayJ]
    exact hcrit
  · rw [hlayJ]
    exact hTYle0
  · rw [hlayJ]
    exact hJpc

end CFSG.LocalAnalysis.GLTheoremA.KD1426AltTen

end
