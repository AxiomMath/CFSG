module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.HardMathSupport.Solomon.LocalBalance.Components

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type*} [Group G]

@[expose] def kerB (p : ℕ) (B J : Subgroup G) : Subgroup G :=
  B ⊓ centralizerQuot J (GLAPPrimeCoreOf p J)

theorem kerB_le (p : ℕ) (B J : Subgroup G) : kerB p B J ≤ B := inf_le_left

theorem mem_oPrimePOf_of_forall_commutator_mem [Finite G] {p : ℕ} (hp : p.Prime)
    {J : Subgroup G} {x : G} (hx : x ∈ J)
    (hc : ∀ y ∈ J, x * y * x⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf p J) : x ∈ oPrimePOf p J := by
  refine ⟨⟨x, hx⟩, ?_, rfl⟩
  show QuotientGroup.mk' (GLAPPrimeCore p ↥J) ⟨x, hx⟩ ∈ CFSG.pCore p (↥J ⧸ GLAPPrimeCore p ↥J)
  refine mem_pCore_of_forall_comm_aux hp fun w => ?_
  obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥J) w
  obtain ⟨c, hc1, hc2⟩ := hc ℓ ℓ.2
  have hcc : c = ⟨x, hx⟩ * ℓ * ⟨x, hx⟩⁻¹ * ℓ⁻¹ := Subtype.ext (by simpa using hc2)
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥J) c = 1 := (QuotientGroup.eq_one_iff _).2 hc1
  rw [hcc, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  set a := QuotientGroup.mk' (GLAPPrimeCore p ↥J) ⟨x, hx⟩
  set b := QuotientGroup.mk' (GLAPPrimeCore p ↥J) ℓ
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

theorem kerB_gLBConj [Finite G] (p : ℕ) {B : Subgroup G} (hB : IsMulCommutative B)
    (J : Subgroup G) {g : G} (hg : g ∈ B) : kerB p B (GLBConj g J) = kerB p B J := by
  ext b
  unfold kerB
  rw [glaPPrimeCoreOf_gLBConj, Subgroup.mem_inf, Subgroup.mem_inf]
  refine and_congr_right fun hbB => ?_
  have hcomm : g * b * g⁻¹ = b := by
    have := congrArg Subtype.val (hB.is_comm.comm ⟨g, hg⟩ ⟨b, hbB⟩)
    simp only [Subgroup.coe_mul] at this
    rw [this]; group
  have hcomm' : g * b⁻¹ * g⁻¹ = b⁻¹ := by
    rw [show g * b⁻¹ * g⁻¹ = (g * b * g⁻¹)⁻¹ by group, hcomm]
  have hid : ∀ y : G, g * (y * b * y⁻¹ * b⁻¹) * g⁻¹ =
      (g * y * g⁻¹) * b * (g * y * g⁻¹)⁻¹ * b⁻¹ := by
    intro y
    calc g * (y * b * y⁻¹ * b⁻¹) * g⁻¹
        = (g * y * g⁻¹) * (g * b * g⁻¹) * (g * y⁻¹ * g⁻¹) * (g * b⁻¹ * g⁻¹) := by group
      _ = _ := by rw [hcomm, hcomm']; group
  show (b ∈ Subgroup.normalizer ((GLBConj g J : Subgroup G) : Set G) ∧
      b ∈ Subgroup.normalizer ((GLBConj g (GLAPPrimeCoreOf p J) : Subgroup G) : Set G) ∧
      ∀ x ∈ GLBConj g J, x * b * x⁻¹ * b⁻¹ ∈ GLBConj g (GLAPPrimeCoreOf p J)) ↔
    (b ∈ Subgroup.normalizer (J : Set G) ∧ b ∈ Subgroup.normalizer (GLAPPrimeCoreOf p J : Set G) ∧
      ∀ x ∈ J, x * b * x⁻¹ * b⁻¹ ∈ GLAPPrimeCoreOf p J)
  rw [normalizer_gLBConj, normalizer_gLBConj, mem_gLBConj, mem_gLBConj, hcomm]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h x hx => ?_, fun h x hx => ?_⟩)
  · have hy : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    have := h (g⁻¹ * x * g) (by rw [mem_gLBConj, hy]; exact hx)
    rwa [mem_gLBConj, hid, hy] at this
  · rw [mem_gLBConj, hid]
    exact h _ (mem_gLBConj.1 hx)

private theorem conj_mem_gLAPPrimeCoreOf {p : ℕ} {J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (J : Set G)) {y : G} (hy : y ∈ GLAPPrimeCoreOf p J) :
    g * y * g⁻¹ ∈ GLAPPrimeCoreOf p J := by
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨J.normalizerMonoidHom ⟨g, hg⟩ y',
    map_gLAPPrimeCore_le p (J.normalizerMonoidHom ⟨g, hg⟩) ⟨y', hy', rfl⟩, ?_⟩
  rfl

private theorem mem_centralizerQuot_iff_barAut (p : ℕ) {J : Subgroup G}
    (g : ↥(Subgroup.normalizer (J : Set G))) :
    (g : G) ∈ centralizerQuot J (GLAPPrimeCoreOf p J) ↔ barAut p J g = 1 := by
  have hs : ∀ y : ↥J, ((J.normalizerMonoidHom g y : ↥J) : G) = g * y * (g : G)⁻¹ := fun _ => rfl
  constructor
  · rintro ⟨-, -, hc⟩
    ext z
    induction z using QuotientGroup.induction_on with | H y => ?_
    rw [barAut_mk, MulAut.one_apply, eq_comm, QuotientGroup.eq]
    have := hc (y : G)⁻¹ (J.inv_mem y.2)
    refine (Subgroup.mem_map_iff_mem J.subtype_injective).1
      (?_ : J.subtype _ ∈ GLAPPrimeCoreOf p J)
    simpa [mul_assoc, hs] using this
  · intro h
    refine ⟨g.2, ?_, fun x hx => ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => conj_mem_gLAPPrimeCoreOf g.2 hy, fun hy => ?_⟩
      have := conj_mem_gLAPPrimeCoreOf (inv_mem g.2) hy
      simpa [mul_assoc] using this
    · have h1 := congrArg (fun φ => φ (QuotientGroup.mk (⟨x, hx⟩⁻¹ : ↥J))) h
      simp only [barAut_mk, MulAut.one_apply] at h1
      rw [eq_comm, QuotientGroup.eq] at h1
      have h2 : J.subtype _ ∈ GLAPPrimeCoreOf p J := Subgroup.mem_map_of_mem J.subtype h1
      simpa [mul_assoc, hs] using h2

theorem relIndex_kerB_le [Finite G] {B J : Subgroup G} (hB : IsElemAbelian 3 B)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 J))) ≤ 2)
    (h3 : (Subgroup.normalizer (J : Set G)).relIndex B = 3) : (kerB 3 B J).relIndex B ≤ 27 := by
  classical
  set N : Subgroup G := B ⊓ Subgroup.normalizer (J : Set G) with hN
  have hNB : N ≤ B := inf_le_left
  have hkN : kerB 3 B J ≤ N := fun x hx => ⟨hx.1, hx.2.1⟩
  let φ : ↥N →* MulAut (barOf 3 J) :=
    (barAut 3 J).comp (Subgroup.inclusion (inf_le_right : N ≤ Subgroup.normalizer (J : Set G)))
  have hker : (kerB 3 B J).subgroupOf N = φ.ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    show (x : G) ∈ kerB 3 B J ↔ barAut 3 J (Subgroup.inclusion _ x) = 1
    rw [← mem_centralizerQuot_iff_barAut]
    exact ⟨fun h => h.2, fun h => ⟨x.2.1, h⟩⟩
  have h1 : (kerB 3 B J).relIndex N = Nat.card φ.range := by
    rw [Subgroup.relIndex, hker, Subgroup.index_ker]
  have h2 : N.relIndex B = 3 := by
    rw [hN, Subgroup.inf_relIndex_left]; exact h3
  have hel : IsElemAbelian 3 φ.range := by
    have := hB.1
    refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
    · rcases u with ⟨_, a, rfl⟩
      rcases v with ⟨_, b, rfl⟩
      refine Subtype.ext ?_
      show φ a * φ b = φ b * φ a
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (setLike_mul_comm (hNB a.2) (hNB b.2))
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ 3 = 1 := Subtype.ext (hB.2 a (hNB a.2))
      rw [this, map_one]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpg : IsPGroup 3 φ.range := fun x => ⟨1, Subtype.ext (by simpa using hel.2 x.1 x.2)⟩
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  have hbdd : BddAbove {k | ∃ E : Subgroup (MulAut (barOf 3 J)), E ≤ ⊤ ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ k} := by
    refine ⟨Nat.card (MulAut (barOf 3 J)), ?_⟩
    rintro k' ⟨E, -, -, hE⟩
    have := Subgroup.card_le_card_group E
    rw [hE] at this
    exact (Nat.lt_pow_self (by norm_num)).le.trans this
  have hle : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 J))) :=
    le_csSup hbdd ⟨φ.range, le_top, hel, hk⟩
  have hk2 : Nat.card φ.range ≤ 9 := by
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (hle.trans hrank)
      _ = 9 := by norm_num
  have h4 := Subgroup.relIndex_mul_relIndex (kerB 3 B J) N B hkN hNB
  rw [h1, h2] at h4
  omega

end CFSG.HardMathSupport.Solomon.LocalBalance
