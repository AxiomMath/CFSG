module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Facts
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267RankAut
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans
import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.CGT.T75P.SylowSplit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

@[expose] def ModelAGen (p n : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (A A₁ A₁₂ J : Subgroup X) (t : X), IsElemAbelian p A ∧ Nat.card A = p ^ n ∧
    A₁ ≤ A₁₂ ∧ A₁₂ ≤ A ∧ Nat.card A₁ = p ∧ Nat.card A₁₂ = p ^ 2 ∧
    GLAPComponent p (Subgroup.centralizer (A₁ : Set X)) J ∧
    A ≤ Subgroup.normalizer (J : Set X) ∧
    (∀ x ∈ A, CentMod p J x → x ∈ A₁) ∧
    GLAPLayer p (J ⊓ Subgroup.centralizer (A₁₂ : Set X)) ≠ ⊥ ∧
    t ≠ 1 ∧ t ^ 2 = 1 ∧ J ≤ Subgroup.centralizer ({t} : Set X) ∧
    A ≤ Subgroup.centralizer ({t} : Set X)

section Helpers

variable {G : Type*} [Group G]

theorem exists_pow_lt_of_pow_eq_one {p : ℕ} (hp : 0 < p) {g y : G} (hg : g ^ p = 1)
    (hy : y ∈ Subgroup.zpowers g) : ∃ k : ℕ, k < p ∧ g ^ k = y := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have h0 : (0 : ℤ) ≤ n % p := Int.emod_nonneg n hp'.ne'
  have hlt : n % p < p := Int.emod_lt_of_pos n hp'
  refine ⟨(n % p).toNat, by omega, ?_⟩
  have e : n = p * (n / p) + n % p := (Int.mul_ediv_add_emod n p).symm
  have hz : (g ^ (n % (p : ℤ)).toNat : G) = g ^ (n % (p : ℤ)) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg h0]
  rw [hz]
  conv_rhs => rw [e]
  rw [zpow_add, zpow_mul, zpow_natCast, hg, one_zpow, one_mul]

theorem mem_centralizer_sup_of_comm {y : G} {H K : Subgroup G} (hH : ∀ h ∈ H, h * y = y * h)
    (hK : ∀ k ∈ K, k * y = y * k) : y ∈ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) := by
  have hle : H ⊔ K ≤ Subgroup.centralizer ({y} : Set G) :=
    sup_le (fun h hh => Subgroup.mem_centralizer_singleton_iff.2 (hH h hh))
      (fun k hk => Subgroup.mem_centralizer_singleton_iff.2 (hK k hk))
  exact Subgroup.mem_centralizer_iff.2 fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

theorem mem_normalizer_of_forall_comm {g : G} {K : Subgroup G} (hg : ∀ k ∈ K, g * k = k * g) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [hg y hy, mul_inv_cancel_right]
    exact hy
  · intro hy
    have e : g * (g * y * g⁻¹) = g * y := by rw [hg _ hy]; group
    rw [mul_left_cancel e] at hy
    exact hy

theorem inf_centralizer_sup_of_comm {H K L : Subgroup G} (hHL : ∀ h ∈ H, ∀ l ∈ L, h * l = l * h) :
    L ⊓ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) =
      L ⊓ Subgroup.centralizer (K : Set G) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_right))
  · rintro y ⟨hyL, hyK⟩
    exact ⟨hyL, mem_centralizer_sup_of_comm (fun h hh => hHL h hh y hyL)
      (fun k hk => Subgroup.mem_centralizer_iff.1 hyK k hk)⟩

theorem map_centralizer_of_injective {X : Type*} [Group X] (φ : X →* G) (hφ : Function.Injective φ)
    (A : Subgroup X) :
    (Subgroup.centralizer (A : Set X)).map φ =
      φ.range ⊓ Subgroup.centralizer ((A.map φ : Subgroup G) : Set G) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 hx) a ha]
  · rintro ⟨⟨x, rfl⟩, hy⟩
    refine ⟨x, Subgroup.mem_centralizer_iff.2 fun a ha => hφ ?_, rfl⟩
    rw [map_mul, map_mul]
    exact (Subgroup.mem_centralizer_iff.1 hy) (φ a) ⟨a, ha, rfl⟩

theorem isPGroup_two_zpowers_of_sq {t : G} (ht2 : t ^ 2 = 1) :
    IsPGroup 2 (Subgroup.zpowers t) := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  have hdvd : orderOf (x : G) ∣ 2 :=
    (orderOf_dvd_of_mem_zpowers x.2).trans (orderOf_dvd_of_pow_eq_one ht2)
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  exact orderOf_dvd_iff_pow_eq_one.1 hdvd

theorem zpowers_ne_bot_of_ne_one {t : G} (ht : t ≠ 1) : Subgroup.zpowers t ≠ ⊥ := fun h => ht (by
  have := Subgroup.mem_zpowers t
  rw [h, Subgroup.mem_bot] at this
  exact this)

end Helpers

section Transport

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem comm_of_mem_centMod (hSn : S.Normal) (hcore : GLAPPrimeCore p ↥S = ⊥) {b : Ω}
    (hb : b ∈ centModSubgroup p S) {s : Ω} (hs : s ∈ S) : b * s = s * b := by
  have h1 := (mem_centModSubgroup.1 hb).2 s hs
  have hmem : ⁅s, b⁆ ∈ S := by
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    exact S.mul_mem hs (by rw [← mul_assoc]; exact hSn.conj_mem _ (S.inv_mem hs) b)
  have h2 := (S267.mem_glaPPrimeCoreOf_iff' (p := p) (S := S) ⟨_, hmem⟩).1 h1
  rw [hcore, Subgroup.mem_bot] at h2
  have h3 : ⁅s, b⁆ = 1 := congrArg Subtype.val h2
  exact ((commutatorElement_eq_one_iff_mul_comm).1 h3).symm

theorem eq_one_of_mem_centMod (hSn : S.Normal) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hZ : Subgroup.center ↥S = ⊥) {s : Ω} (hs : s ∈ S) (hc : s ∈ centModSubgroup p S) : s = 1 := by
  have h : (⟨s, hs⟩ : ↥S) ∈ Subgroup.center ↥S := Subgroup.mem_center_iff.2 fun g =>
    Subtype.ext (comm_of_mem_centMod hSn hcore hc g.2).symm
  rw [hZ, Subgroup.mem_bot] at h
  exact congrArg Subtype.val h

theorem concA_of_modelAGen {n : ℕ} (hp : p.Prime) (hn : 3 ≤ n) (hSn : S.Normal)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hZ : Subgroup.center ↥S = ⊥) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) (hBn : Nat.card B ≤ p ^ (n + 1))
    {X : Type} [Group X] [Finite X] (φ : X →* Ω) (hφ : Function.Injective φ) (hφS : φ.range = S)
    (hM : ModelAGen p n X) : S267ConcA p S B := by
  obtain ⟨A, A₁, A₁₂, J, t, hA, hAc, h1, h12, hA₁c, hA₁₂c, hJ, hAN, hcent, hlay, ht1, ht2, hJt,
    hAt⟩ := hM
  haveI : Fact p.Prime := ⟨hp⟩
  set B₀ := B ⊓ centModSubgroup p S with hB₀
  have hmapS : ∀ (K : Subgroup X), K.map φ ≤ S := fun K => by
    rw [← hφS]
    exact Subgroup.map_le_range φ K
  have hB₀S : ∀ b ∈ B₀, ∀ s ∈ S, b * s = s * b := fun b hb s hs =>
    comm_of_mem_centMod hSn hcore hb.2 hs
  have hB₀el : IsElemAbelian p B₀ := hB.mono inf_le_left
  have hcomm : ∀ (K : Subgroup X), ∀ b ∈ B₀, ∀ a ∈ K.map φ, b * a = a * b := fun K b hb a ha =>
    hB₀S b hb a (hmapS K ha)
  have hinf : ∀ (K : Subgroup X), B₀ ⊓ K.map φ = ⊥ := fun K => by
    rw [eq_bot_iff]
    rintro x ⟨hx₀, hx⟩
    exact (Subgroup.mem_bot).2 (eq_one_of_mem_centMod hSn hcore hZ (hmapS K hx) hx₀.2)
  have hcard : ∀ (K : Subgroup X), Nat.card ↥(B₀ ⊔ K.map φ) = p * Nat.card K := fun K => by
    rw [CFSG.CGT.T75P.card_sup_of_commute (hcomm K) (hinf K), hBC,
      Subgroup.card_map_of_injective hφ]
  set B' := B₀ ⊔ A.map φ with hB'
  set D := B₀ ⊔ A₁.map φ with hD
  set E := B₀ ⊔ A₁₂.map φ with hE
  set Jφ := J.map φ with hJφ
  have hAφ : IsElemAbelian p (A.map φ) := CFSG.SectionRank.isElemAbelian_map hA φ
  have hB'el : IsElemAbelian p B' := hB₀el.sup_of_commute hAφ (hcomm A)
  have hB'c : Nat.card B' = p ^ (n + 1) := by rw [hB', hcard, hAc, pow_succ']
  have hDc : Nat.card D = p ^ 2 := by rw [hD, hcard, hA₁c, sq]
  have hEc : Nat.card E = p ^ 3 := by rw [hE, hcard, hA₁₂c]; ring
  have hDB' : D ≤ B' := sup_le_sup_left (Subgroup.map_mono (h1.trans h12)) _
  have hEB' : E ≤ B' := sup_le_sup_left (Subgroup.map_mono h12) _
  have hDE : D ≤ E := sup_le_sup_left (Subgroup.map_mono h1) _
  have hJS : Jφ ≤ S := hmapS J
  have hJA₁ : J ≤ Subgroup.centralizer (A₁ : Set X) := hJ.1
  have htS : φ t ∈ S := hφS ▸ ⟨t, rfl⟩
  have hSD : S ⊓ Subgroup.centralizer (D : Set Ω) =
      (Subgroup.centralizer (A₁ : Set X)).map φ := by
    rw [hD, inf_centralizer_sup_of_comm (fun b hb s hs => hB₀S b hb s hs),
      map_centralizer_of_injective φ hφ, hφS]
  have hJE : Jφ ⊓ Subgroup.centralizer (E : Set Ω) =
      (J ⊓ Subgroup.centralizer (A₁₂ : Set X)).map φ := by
    rw [hE, inf_centralizer_sup_of_comm (fun b hb s hs => hB₀S b hb s (hJS hs)),
      Subgroup.map_inf_eq _ _ φ hφ, map_centralizer_of_injective φ hφ, ← inf_assoc,
      inf_eq_left.2 (show Jφ ≤ φ.range from hφS ▸ hJS)]
  have hB'N : B' ≤ Subgroup.normalizer (Jφ : Set Ω) := by
    refine sup_le (fun b hb => mem_normalizer_of_forall_comm fun k hk => hB₀S b hb k (hJS hk)) ?_
    rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.le_normalizer_map φ ⟨a, hAN ha, rfl⟩
  have hDcent : D ≤ Subgroup.centralizer (Jφ : Set Ω) := by
    refine sup_le (fun b hb => Subgroup.mem_centralizer_iff.2 fun j hj =>
      (hB₀S b hb j (hJS hj)).symm) ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨j, hj, rfl⟩
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 (hJA₁ hj)) a ha]
  have hcentD : ∀ b ∈ B', CentMod p Jφ b ↔ b ∈ D := by
    intro b hb
    constructor
    · intro hc
      obtain ⟨b₀, hb₀, _, ⟨a, ha, rfl⟩, rfl⟩ :=
        CFSG.GH74.Uniqueness.SU.SU1.mem_sup_of_commute (hcomm A) hb
      have hb₀c : b₀ ∈ centModSubgroup p Jφ := centMod_iff.1 (centMod_of_mem_centralizer
        (Subgroup.mem_centralizer_iff.2 fun j hj => (hB₀S b₀ hb₀ j (hJS hj)).symm))
      have hac : CentMod p Jφ (φ a) := by
        have e : φ a = b₀⁻¹ * (b₀ * φ a) := by group
        rw [e]
        exact centMod_iff.2 ((centModSubgroup p Jφ).mul_mem
          ((centModSubgroup p Jφ).inv_mem hb₀c) (centMod_iff.1 hc))
      have hax : a ∈ A₁ :=
        hcent a ha ((CFSG.LocalAnalysis.GLTheoremA.T123C.centMod_map_iff hφ p J a).1 hac)
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb₀)
        (Subgroup.mem_sup_right ⟨a, hax, rfl⟩)
    · intro hbD
      exact centMod_of_mem_centralizer (hDcent hbD)
  have hEl : GLAPLayer p (Jφ ⊓ Subgroup.centralizer (E : Set Ω)) ≠ ⊥ := by
    rw [hJE]
    exact CFSG.LocalAnalysis.GLTheoremA.I2611.glaPLayer_map_ne_bot hp φ hφ hlay
  have hB'C : B' ⊓ centModSubgroup p S = B₀ := by
    apply le_antisymm
    · rintro b ⟨hb, hbC⟩
      obtain ⟨b₀, hb₀, _, ⟨a, ha, rfl⟩, rfl⟩ :=
        CFSG.GH74.Uniqueness.SU.SU1.mem_sup_of_commute (hcomm A) hb
      have haC : φ a ∈ centModSubgroup p S := by
        have e : φ a = b₀⁻¹ * (b₀ * φ a) := by group
        rw [e]
        exact (centModSubgroup p S).mul_mem ((centModSubgroup p S).inv_mem hb₀.2) hbC
      rw [eq_one_of_mem_centMod hSn hcore hZ (hmapS A ⟨a, ha, rfl⟩) haC, mul_one]
      exact hb₀
    · exact le_inf le_sup_left inf_le_right
  have hB'cent : B' ≤ Subgroup.centralizer ({φ t} : Set Ω) := by
    refine sup_le (fun b hb => Subgroup.mem_centralizer_singleton_iff.2 (hB₀S b hb _ htS)) ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 (hAt ha)]
  have htφ1 : φ t ≠ 1 := fun h => ht1 (hφ (h.trans (map_one φ).symm))
  have htφ2 : φ t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hB'T : B' ≤ Subgroup.normalizer ((Subgroup.zpowers (φ t) : Subgroup Ω) : Set Ω) := by
    intro b hb
    refine mem_normalizer_of_forall_comm fun k hk => ?_
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 (hB'cent hb)) m).eq
  have h4 : p ^ 2 * p ^ 2 ≤ p ^ (n + 1) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  refine ⟨B', D, Jφ, hB'el, ⟨⟨hDB', by rw [hDc], by rw [hDc, hB'c]; exact h4⟩,
    ⟨by rw [hSD, hJφ, CFSG.LocalAnalysis.GLTheoremA.T123C.glaPComponent_map_iff hφ]; exact hJ,
      hB'N, hcentD⟩,
    fun _ => ⟨E, hEB', hB'el.mono hEB', hEc, hDE, hEl⟩⟩,
    Or.inr ⟨by rw [hB'c]; exact hBn, Subgroup.zpowers (φ t), zpowers_ne_bot_of_ne_one htφ1,
      isPGroup_two_zpowers_of_sq htφ2, hB'T⟩,
    by rw [hB'C, hBC], φ t, htφ1, htφ2, fun d hd => ?_, fun j hj => ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.1 (hB'cent (hDB' hd))
  · obtain ⟨j', hj', rfl⟩ := hj
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 (hJt hj')]

end Transport

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
