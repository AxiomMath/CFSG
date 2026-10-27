module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426AltTen
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426MaxRank
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltUtil
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement
open CFSG.LocalAnalysis.GLTheoremA.KD1426Common

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426AltTenCore

variable {Y : Type} [Group Y] [Finite Y]

theorem psiHom_equiv {n : ℕ} (K : Subgroup Y) (hK : K.Normal) (e : K ≃* alternatingGroup (Fin n))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n) (B : Subgroup Y) (hB : ∀ b ∈ B, b ^ p = 1)
    (b : B) (k : K) :
    e (KD264Inner.conjKequiv K hK (b : Y) k) =
      KD264Inner.psiHom K hK e hp hp2 hn B hB b * e k *
        (KD264Inner.psiHom K hK e hp hp2 hn B hB b)⁻¹ := by
  rw [KD264Inner.psiHom_apply K hK e hp hp2 hn B hB b,
    ← KD264Inner.alphaHom_apply_coe K hK e (b : Y) k]
  exact KD264Inner.alpha_apply_eq_conj K hK e hp hp2 hn B hB b (e k)

theorem card_sup_three_cycle {K B : Subgroup Y} (hK : K.Normal)
    (hB : CFSG.Open.IsElemAbelian 3 B) (ψ : ↥B →* alternatingGroup (Fin 10))
    (hψker : ∀ b : ↥B, ψ b = 1 ↔ (b : Y) ∈ Subgroup.centralizer (K : Set Y))
    (a : ↥B) (hσ1 : ψ a ≠ 1) :
    Nat.card ↥(Subgroup.zpowers (a : Y) ⊔ (B ⊓ Subgroup.centralizer (K : Set Y))) =
      3 * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) := by
  classical
  have hB3 : ∀ b ∈ B, b ^ 3 = 1 := hB.2
  have ha3' : (a : Y) ^ 3 = 1 := hB3 (a : Y) a.2
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
          _ = (h * b) * b⁻¹ := by rw [← KD1426AltTen.comm_zpowers hab hh]
          _ = h := by group
      rw [e]
      exact hh
    · intro hg
      have hc := KD1426AltTen.comm_zpowers hab hg
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
  exact KD1426AltTen.card_sup_zpowers hza hnorm0 hBz

theorem layer_ne_bot_of_three_cycle {K B : Subgroup Y} (hK : K.Normal)
    (hB : CFSG.Open.IsElemAbelian 3 B) (π : ↥K ≃* alternatingGroup (Fin 10))
    (ψ : ↥B →* alternatingGroup (Fin 10))
    (hψequiv : ∀ (b : ↥B) (k : ↥K), π (KD264Inner.conjKequiv K hK (b : Y) k) = ψ b * π k * (ψ b)⁻¹)
    (a : ↥B) (ha : ((ψ a : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)).support.card = 3) :
    GLAPLayer 3 (K ⊓ Subgroup.centralizer
      ((Subgroup.zpowers (a : Y) ⊔ (B ⊓ Subgroup.centralizer (K : Set Y)) : Subgroup Y) : Set Y)) ≠ ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσ3 : ψ a ^ 3 = 1 := by
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (hB.2 (a : Y) a.2)
    rw [this, map_one]
  obtain ⟨-, hlayJ⟩ := KD1426AltTen.layer_sup (B0 := B ⊓ Subgroup.centralizer (K : Set Y)) hK π
    (a : Y) (ψ a) hσ3 ha (fun k => hψequiv a k) (fun b hb => (Subgroup.mem_inf.1 hb).2)
  obtain ⟨J, hJ⟩ : ∃ J : Subgroup Y, J = ((altFix ((ψ a : alternatingGroup (Fin 10)) :
      Equiv.Perm (Fin 10))).comap π.toMonoidHom).map K.subtype := ⟨_, rfl⟩
  rw [← hJ] at hlayJ
  obtain ⟨-, -, hJc⟩ := KD1426AltTenJ.J_pSimple π ha hJ
  rw [hlayJ]
  intro h
  rw [h, Subgroup.card_bot] at hJc
  norm_num at hJc

theorem alt10_core {K B : Subgroup Y} (hK : K.Normal) (hq : CFSG.Open.IsQuasisimple ↥K)
    (eK : ↥K ⧸ Subgroup.center ↥K ≃* alternatingGroup (Fin 10))
    (hcore : GLAPPrimeCore 3 ↥K = ⊥) (hB : CFSG.Open.IsElemAbelian 3 B)
    (hcard : 3 ^ 4 ≤ Nat.card B) (hmax : IsMaxRankIn 3 B ⊤)
    (hC : B ⊓ Subgroup.centralizer (K : Set Y) ≠ ⊥)
    (hH : ∀ E : Subgroup Y, E ≤ B → CFSG.Open.IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      GLAPLayer 3 (K ⊓ Subgroup.centralizer (E : Set Y)) = ⊥) :
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
  have hZ : Subgroup.center ↥K = ⊥ := KD1426AltTen.center_bot_of_ten hq hcore eK
  let eQ : ↥K ⧸ Subgroup.center ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let π : ↥K ≃* alternatingGroup (Fin 10) := eQ.symm.trans eK
  have hK3 : ∀ b ∈ B, b ^ 3 = 1 := hB.2
  let ψ : ↥B →* alternatingGroup (Fin 10) :=
    KD264Inner.psiHom K hK π Nat.prime_three (by norm_num) (by norm_num) B hK3
  have hψequiv : ∀ (b : ↥B) (k : ↥K),
      π (KD264Inner.conjKequiv K hK (b : Y) k) = ψ b * π k * (ψ b)⁻¹ :=
    fun b k => psiHom_equiv K hK π Nat.prime_three (by norm_num) (by norm_num) B hK3 b k
  have hψker : ∀ b : ↥B, ψ b = 1 ↔ (b : Y) ∈ Subgroup.centralizer (K : Set Y) :=
    fun b => KD264Inner.psiHom_eq_one_iff K hK π Nat.prime_three (by norm_num) (by norm_num) B hK3 b
  have hCel : CFSG.Open.IsElemAbelian 3 (B ⊓ Subgroup.centralizer (K : Set Y)) :=
    isElemAbelian_of_le inf_le_left hB
  have hkerC : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = Nat.card ψ.ker :=
    KD264Rank.card_inf_centralizer_eq_ker Nat.prime_three (by norm_num) (by norm_num) K hK π B hB
  have hsplit : Nat.card ψ.ker * Nat.card ψ.range = Nat.card B :=
    Subgroup.card_ker_mul_card_range ψ
  have hPel : CFSG.Open.IsElemAbelian 3 ψ.range := isElemAbelian_range hB ψ
  have hCp : IsPGroup 3 ↥(B ⊓ Subgroup.centralizer (K : Set Y)) :=
    fun g => ⟨1, Subtype.ext (by simpa using hCel.2 g.1 g.2)⟩
  have hPp : IsPGroup 3 ↥ψ.range := fun g => ⟨1, Subtype.ext (by simpa using hPel.2 g.1 g.2)⟩
  obtain ⟨c, hc⟩ := hCp.exists_card_eq
  obtain ⟨m, hm⟩ := hPp.exists_card_eq
  have hP'el : CFSG.Open.IsElemAbelian 3 (ψ.range.map (alternatingGroup (Fin 10)).subtype) :=
    KD264Util.isElemAbelian_map_of_hom hPel _
  have hP'card : Nat.card ↥(ψ.range.map (alternatingGroup (Fin 10)).subtype) =
      Nat.card ψ.range :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  obtain ⟨hPle, hPex⟩ := KD1426AltTenPerm.orbit_bound_A10 hP'el
  rw [hP'card] at hPle hPex
  rw [hm] at hPle
  have hm3 : m ≤ 3 := by
    have h27 : 3 ^ m ≤ 3 ^ 3 := by simpa using hPle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h27
  have hBcard : Nat.card B = 3 ^ c * 3 ^ m := by
    rw [← hsplit, ← hkerC, hc, hm]
  have hc4 : 4 ≤ c + m := by
    have h1 : 3 ^ 4 ≤ 3 ^ (c + m) := by
      rw [pow_add, ← hBcard]
      exact hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h1
  have hc2 : c ≤ 2 := by
    by_contra hc3
    obtain ⟨E, hEcard, -, hEC⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three
      (H := (⊥ : Subgroup Y)) (L := B ⊓ Subgroup.centralizer (K : Set Y)) (n := 3) (by simp)
      (by rw [hc]; exact pow_dvd_pow 3 (by omega)) bot_le
    have hEB : E ≤ B := hEC.trans inf_le_left
    have hEel : CFSG.Open.IsElemAbelian 3 E := isElemAbelian_of_le hEB hB
    have hKE : K ⊓ Subgroup.centralizer (E : Set Y) = K := by
      apply inf_eq_left.2
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hEC he)).2 k hk).symm
    have h1 := hH E hEB hEel hEcard
    rw [hKE, glaPLayer_eq_self hq hcore] at h1
    have h2 : Nat.card ↥K = 1 := by rw [h1, Subgroup.card_bot]
    have h3 : Nat.card ↥K = 1814400 := by
      rw [Nat.card_congr π.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      norm_num [Nat.factorial]
    omega
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · exfalso
      have hCtriv : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = 1 := by
        rw [hc, h0, pow_zero]
      exact hC (Subgroup.eq_bot_of_card_eq _ hCtriv)
    · exact h0
  have hcases : (c = 1 ∧ m = 3) ∨ (c = 2 ∧ m = 2) ∨ (c = 2 ∧ m = 3) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
    have hB0c : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = 3 := by
      rw [hc] <;> norm_num
    have hPc : Nat.card ψ.range = 27 := by
      rw [hm] <;> norm_num
    have hcardB : Nat.card B = 3 ^ 4 := by
      rw [hBcard] <;> norm_num
    obtain ⟨a', ha'P, ha'supp⟩ := hPex (le_of_eq hPc.symm)
    obtain ⟨y, hyP, hya⟩ := Subgroup.mem_map.1 ha'P
    obtain ⟨a0, ha0⟩ := MonoidHom.mem_range.1 hyP
    have ha0supp : ((ψ a0 : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)).support.card = 3 := by
      have hval : ((ψ a0 : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)) = a' := by
        rw [ha0]
        exact hya
      rw [hval]
      exact ha'supp
    exact KD1426AltTen.alt10_main hK hB hcardB π ψ hψequiv hψker hB0c hPc a0 ha0supp
  ·
    exfalso
    have hB0c9 : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = 9 := by
      rw [hc] <;> norm_num
    have hBcard81 : Nat.card B = 81 := by
      rw [hBcard] <;> norm_num
    let f : alternatingGroup (Fin 10) →* Y := K.subtype.comp π.symm.toMonoidHom
    have hf : Function.Injective f := K.subtype_injective.comp π.symm.injective
    have hHel : CFSG.Open.IsElemAbelian 3 (KD1426E27.W10.map f) :=
      KD264Rank.isElemAbelian_map hf KD1426E27.W10_elemAbelian
    have hHcard : 27 ≤ Nat.card ↥(KD1426E27.W10.map f) := by
      rw [Subgroup.card_map_of_injective hf]
      exact KD1426E27.card_W10_ge
    have hHc : ∀ h ∈ KD1426E27.W10.map f, ∀ b ∈ B ⊓ Subgroup.centralizer (K : Set Y),
        h * b = b * h := by
      intro h hh b hb
      obtain ⟨w, -, rfl⟩ := Subgroup.mem_map.1 hh
      exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hb).2 _ (π.symm w).2
    have hHdisj : KD1426E27.W10.map f ⊓ (B ⊓ Subgroup.centralizer (K : Set Y)) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨w, -, rfl⟩ := Subgroup.mem_map.1 hxH
      have hz : π.symm w ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        show (g : Y) * ((π.symm w : K) : Y) = ((π.symm w : K) : Y) * (g : Y)
        exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hxC).2 (g : Y) g.2
      rw [hZ, Subgroup.mem_bot] at hz
      rw [Subgroup.mem_bot]
      show ((π.symm w : K) : Y) = 1
      simp [hz]
    have hmr := KD1426MaxRank.max_rank_bound hB hmax hHel inf_le_left hHc hHdisj
    rw [hB0c9, hBcard81] at hmr
    have h27 : 27 * 9 ≤ Nat.card ↥(KD1426E27.W10.map f) * 9 := Nat.mul_le_mul_right 9 hHcard
    omega
  ·
    exfalso
    have hB0c9 : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = 9 := by
      rw [hc] <;> norm_num
    have hPc : Nat.card ψ.range = 27 := by
      rw [hm] <;> norm_num
    obtain ⟨a', ha'P, ha'supp⟩ := hPex (le_of_eq hPc.symm)
    obtain ⟨y, hyP, hya⟩ := Subgroup.mem_map.1 ha'P
    obtain ⟨a0, ha0⟩ := MonoidHom.mem_range.1 hyP
    have ha0supp : ((ψ a0 : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)).support.card = 3 := by
      have hval : ((ψ a0 : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)) = a' := by
        rw [ha0]
        exact hya
      rw [hval]
      exact ha'supp
    have hσ1 : ψ a0 ≠ 1 := by
      intro h
      rw [h] at ha0supp
      simp at ha0supp
    have hE := card_sup_three_cycle hK hB ψ hψker a0 hσ1
    have hEB : Subgroup.zpowers (a0 : Y) ⊔ (B ⊓ Subgroup.centralizer (K : Set Y)) ≤ B :=
      sup_le (Subgroup.zpowers_le.2 a0.2) inf_le_left
    have hEel : CFSG.Open.IsElemAbelian 3
        (Subgroup.zpowers (a0 : Y) ⊔ (B ⊓ Subgroup.centralizer (K : Set Y))) :=
      isElemAbelian_of_le hEB hB
    have hEcard : Nat.card ↥(Subgroup.zpowers (a0 : Y) ⊔ (B ⊓ Subgroup.centralizer (K : Set Y))) =
        3 ^ 3 := by
      rw [hE, hB0c9] <;> norm_num
    have hHE := hH _ hEB hEel hEcard
    exact layer_ne_bot_of_three_cycle hK hB π ψ hψequiv a0 ha0supp hHE

end CFSG.LocalAnalysis.GLTheoremA.KD1426AltTenCore

end
