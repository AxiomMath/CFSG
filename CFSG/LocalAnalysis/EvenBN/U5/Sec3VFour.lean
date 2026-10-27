module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M2
import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelRadicals
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.Common

section Generic

theorem injOn_mk'_of_isPGroup {H : Type*} [Group H] [Finite H] {O : Subgroup H} [O.Normal]
    (hO : Odd (Nat.card O)) {Q : Subgroup H} (hQ : IsPGroup 2 Q) :
    Set.InjOn (QuotientGroup.mk' O) (Q : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx y hy hxy
  have h1 : x⁻¹ * y ∈ O := QuotientGroup.eq.mp hxy
  have h2 : x⁻¹ * y ∈ Q := Q.mul_mem (Q.inv_mem hx) hy
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hQ ⟨_, h2⟩
  rw [Subgroup.orderOf_mk] at hk
  have h3 : orderOf (x⁻¹ * y) ∣ Nat.card O := by
    have := orderOf_dvd_natCard (⟨_, h1⟩ : O)
    rwa [Subgroup.orderOf_mk] at this
  rw [hk] at h3
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans h3))
  rw [hk0, pow_zero] at hk
  exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp hk)

open CFSG.OddStandard.Seitz77 FieldFourCover in
private theorem mul_self_eq_one_of_commute_unipAll {F : Type} [Field F] [CharP F 2]
    {u u₁ u₂ : unipAll F} (h1 : u * u₁ = u₁ * u) (h2 : u * u₂ = u₂ * u)
    (h12 : u₁ * u₂ ≠ u₂ * u₁) : u * u = 1 := by
  rw [commute_unipAll_iff'] at h1 h2
  rw [Ne, commute_unipAll_iff'] at h12
  have hdet : coordA u₁ * coordB u₂ - coordA u₂ * coordB u₁ ≠ 0 := sub_ne_zero.2 h12
  have hB : coordB u = 0 := by
    have e : coordB u * (coordA u₁ * coordB u₂ - coordA u₂ * coordB u₁) = 0 := by
      linear_combination coordB u₁ * h2 - coordB u₂ * h1
    exact (mul_eq_zero.1 e).resolve_right hdet
  exact (sq_eq_one_iff u).2 (Or.inl ((mem_radOne u).2 hB))

theorem eq_one_of_mem_of_pow_two_pow {H : Type*} [Group H] [Finite H] {O : Subgroup H}
    (hO : Odd (Nat.card O)) {y : H} (hy : y ∈ O) {k : ℕ} (hk : y ^ 2 ^ k = 1) : y = 1 := by
  have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf y ∣ Nat.card O := by
    have := orderOf_dvd_natCard (⟨y, hy⟩ : O)
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (2 ^ k) (Nat.card O) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hO)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

end Generic

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem card_le_of_le_image_N₂ {R : Subgroup (centralizer (d.I₂ : Set G) ⧸
      standardComponentOddCore (centralizer (d.I₂ : Set G)))}
    (hR : R ≤ (d.N₂.subgroupOf (centralizer (d.I₂ : Set G))).map
      (QuotientGroup.mk' (standardComponentOddCore (centralizer (d.I₂ : Set G)))))
    (hR2 : IsPGroup 2 R) : Nat.card R ≤ (2 ^ f) ^ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hR2
  have h1 : Nat.card R ∣ Nat.card (hypSU h 1 1) := by
    refine (card_dvd_of_le hR).trans ((card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (subgroupOfEquivOfLe d.N₂_le_centralizer_I₂).toEquiv,
      Nat.card_congr d.N₂equiv.symm.toEquiv]
  obtain ⟨hU, ⟨Q, hQ⟩, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) (by norm_num)
    (by norm_num)
  have h2 := Q.pow_dvd_card_of_pow_dvd_card (p := 2) (n := m) (hm ▸ h1)
  rw [hQ, hU] at h2
  norm_num at h2
  rw [hm]
  exact Nat.le_of_dvd (by positivity) h2

theorem Hyp.mul_self_eq_one_of_mem_V (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) {v : G} (hv : v ∈ d.V) : v * v = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hout, -⟩ := hd.sec3_3_two hGMS
  set H := centralizer (d.I₂ : Set G) with hH
  set O := standardComponentOddCore H with hO
  set θ := QuotientGroup.mk' O with hθ
  set J := d.N₂.subgroupOf H with hJ
  set Jb := J.map θ with hJb
  set D := normalClosure (Jb : Set (H ⧸ O)) with hD
  have hOodd : Odd (Nat.card O) := GMSK.odd_card_standardComponentOddCore H
  have hN₂H : d.N₂ ≤ H := d.N₂_le_centralizer_I₂
  set C₅ := d.P ⊓ centralizer (d.I₅ : Set G) with hC₅
  have hC₅N₅ : C₅ ≤ d.N₅ := by
    rw [hC₅, hd.P_inf_centralizer_I₅]
    exact d.C₅_le_N₅
  have hrV : ∀ w (hw : w ∈ d.V), d.r * w * d.r⁻¹ ∈ H := fun w hw =>
    d.conj_r_mem_centralizer_I₂ (hd.V_le_centralizer_I₅ hw)
  have hrC : ∀ c (hc : c ∈ C₅), d.r * c * d.r⁻¹ ∈ d.N₂ := fun c hc =>
    d.conj_r_mem_N₂ (hC₅N₅ hc)
  set Cr : Subgroup G := C₅.map (MulAut.conj d.r).toMonoidHom with hCr
  have hCrH : Cr ≤ H := by
    rintro _ ⟨c, hc, rfl⟩
    exact hN₂H (hrC c hc)
  have hCr2 : IsPGroup 2 (Cr.subgroupOf H) :=
    ((d.isPGroup_P.to_le inf_le_left).map _).of_equiv (subgroupOfEquivOfLe hCrH).symm
  have hinjCr := injOn_mk'_of_isPGroup hOodd hCr2
  set Qb : Subgroup (H ⧸ O) := (Cr.subgroupOf H).map θ with hQb
  have hcQ : ∀ c (hc : c ∈ C₅), θ ⟨d.r * c * d.r⁻¹, hN₂H (hrC c hc)⟩ ∈ Qb :=
    fun c hc => ⟨_, mem_subgroupOf.2 ⟨c, hc, rfl⟩, rfl⟩
  have hmemQb : ∀ y ∈ Qb, ∃ c, ∃ hc : c ∈ C₅, y = θ ⟨d.r * c * d.r⁻¹, hN₂H (hrC c hc)⟩ := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, hc, hce⟩ := mem_subgroupOf.1 hy
    exact ⟨c, hc, congrArg θ (Subtype.ext hce.symm)⟩
  have hcJ : ∀ c (hc : c ∈ C₅), θ ⟨d.r * c * d.r⁻¹, hN₂H (hrC c hc)⟩ ∈ Jb :=
    fun c hc => ⟨_, mem_subgroupOf.2 (hrC c hc), rfl⟩
  have hQbJ : Qb ≤ Jb := fun y hy => by
    obtain ⟨c, hc, rfl⟩ := hmemQb y hy
    exact hcJ c hc
  have hQb2 : IsPGroup 2 Qb := hCr2.map _
  have hcardQb : Nat.card Qb = (2 ^ f) ^ 3 := by
    have hinjQ : Function.Injective (θ.subgroupMap (Cr.subgroupOf H)) := fun a b hab =>
      Subtype.ext (hinjCr a.2 b.2 (congrArg Subtype.val hab))
    rw [← Nat.card_congr (Equiv.ofBijective _ ⟨hinjQ, θ.subgroupMap_surjective _⟩),
      Nat.card_congr (subgroupOfEquivOfLe hCrH).toEquiv,
      card_map_of_injective (MulAut.conj d.r).injective, hd.card_C₅]
  have hinjC : ∀ c (hc : c ∈ C₅) c' (hc' : c' ∈ C₅),
      θ ⟨d.r * c * d.r⁻¹, hN₂H (hrC c hc)⟩ * θ ⟨d.r * c' * d.r⁻¹, hN₂H (hrC c' hc')⟩ =
        θ ⟨d.r * c' * d.r⁻¹, hN₂H (hrC c' hc')⟩ * θ ⟨d.r * c * d.r⁻¹, hN₂H (hrC c hc)⟩ →
        c * c' = c' * c := by
    intro c hc c' hc' e
    rw [← map_mul, ← map_mul] at e
    have hcX : (⟨d.r * c * d.r⁻¹, hN₂H (hrC c hc)⟩ : H) ∈ Cr.subgroupOf H :=
      mem_subgroupOf.2 ⟨c, hc, rfl⟩
    have hc'X : (⟨d.r * c' * d.r⁻¹, hN₂H (hrC c' hc')⟩ : H) ∈ Cr.subgroupOf H :=
      mem_subgroupOf.2 ⟨c', hc', rfl⟩
    have e'' := congrArg Subtype.val (hinjCr (mul_mem hcX hc'X) (mul_mem hc'X hcX) e)
    simp only [coe_mul] at e''
    have e3 : d.r * (c * c') * d.r⁻¹ = d.r * (c' * c) * d.r⁻¹ := by
      calc d.r * (c * c') * d.r⁻¹ = d.r * c * d.r⁻¹ * (d.r * c' * d.r⁻¹) := by group
        _ = d.r * c' * d.r⁻¹ * (d.r * c * d.r⁻¹) := e''
        _ = d.r * (c' * c) * d.r⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e3)
  have hDn : D.Normal := normalClosure_normal
  have hJD : Jb ≤ D := subset_normalClosure
  obtain ⟨j, hj, hjV⟩ := hd.exists_V_eq_commutator_mul
  have hjN₂ : d.r * j * d.r⁻¹ ∈ d.N₂ := d.conj_r_mem_N₂ hj.1
  have hvD : θ ⟨d.r * v * d.r⁻¹, hrV v hv⟩ ∈ D := by
    obtain ⟨w₀, hw₀, z, hz, hvz⟩ := hjV v hv
    have hzC : z ∈ C₅ := hd.Zp_le_C₅ hz
    have e : (⟨d.r * v * d.r⁻¹, hrV v hv⟩ : H) =
        (⟨d.r * j * d.r⁻¹, hN₂H hjN₂⟩ : H) * ((⟨d.r * w₀ * d.r⁻¹, hrV w₀ hw₀⟩ : H) *
          (⟨d.r * j * d.r⁻¹, hN₂H hjN₂⟩ : H)⁻¹ * (⟨d.r * w₀ * d.r⁻¹, hrV w₀ hw₀⟩ : H)⁻¹) *
          (⟨d.r * z * d.r⁻¹, hN₂H (hrC z hzC)⟩ : H) := by
      apply Subtype.ext
      simp only [coe_mul, coe_inv]
      rw [hvz]
      group
    have hj'D : θ ⟨d.r * j * d.r⁻¹, hN₂H hjN₂⟩ ∈ D :=
      hJD ⟨_, mem_subgroupOf.2 hjN₂, rfl⟩
    rw [e, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact mul_mem (mul_mem hj'D (hDn.conj_mem _ (inv_mem hj'D) _)) (hJD (hcJ z hzC))
  have hcomm : ∀ c (hc : c ∈ C₅),
      θ ⟨d.r * v * d.r⁻¹, hrV v hv⟩ * θ ⟨d.r * c * d.r⁻¹, hN₂H (hrC c hc)⟩ =
        θ ⟨d.r * c * d.r⁻¹, hN₂H (hrC c hc)⟩ * θ ⟨d.r * v * d.r⁻¹, hrV v hv⟩ := by
    intro c hc
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have e := mem_centralizer_iff.1 (hd.CB₄I₃_le_centralizer_C₅ (hd.V_le_CB₄I₃ hv)) c hc
    simp only [coe_mul]
    calc d.r * v * d.r⁻¹ * (d.r * c * d.r⁻¹) = d.r * (v * c) * d.r⁻¹ := by group
      _ = d.r * (c * v) * d.r⁻¹ := by rw [e]
      _ = d.r * c * d.r⁻¹ * (d.r * v * d.r⁻¹) := by group
  have hB₄2 : IsPGroup 2 d.B₄ := by
    rw [B₄_eq_oTwo]
    exact CFSG.EvenSmallLie.UnitarySix.YamadaD.isPGroup_oTwo _
  obtain ⟨k, hk⟩ := hB₄2 ⟨v, (hd.V_le_CB₄I₃.trans d.CB₄I₃_le) hv⟩
  have hvk : v ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hrvk : (⟨d.r * v * d.r⁻¹, hrV v hv⟩ : H) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    rw [coe_pow, coe_one, conj_pow, hvk, mul_one, mul_inv_cancel]
  have hxk : θ ⟨d.r * v * d.r⁻¹, hrV v hv⟩ ^ 2 ^ k = 1 := by rw [← map_pow, hrvk, map_one]
  suffices hsq : θ ⟨d.r * v * d.r⁻¹, hrV v hv⟩ * θ ⟨d.r * v * d.r⁻¹, hrV v hv⟩ = 1 by
    rw [← map_mul] at hsq
    have hO' := (QuotientGroup.eq_one_iff _).1 hsq
    have hk2 : ((⟨d.r * v * d.r⁻¹, hrV v hv⟩ : H) * ⟨d.r * v * d.r⁻¹, hrV v hv⟩) ^ 2 ^ k = 1 := by
      rw [← pow_two, ← pow_mul, mul_comm, pow_mul, hrvk, one_pow]
    have e := congrArg Subtype.val (eq_one_of_mem_of_pow_two_pow hOodd hO' hk2)
    simp only [coe_mul, coe_one] at e
    have e' : d.r * (v * v) * d.r⁻¹ = 1 := by
      calc d.r * (v * v) * d.r⁻¹ = d.r * v * d.r⁻¹ * (d.r * v * d.r⁻¹) := by group
        _ = 1 := e
    calc v * v = d.r⁻¹ * (d.r * (v * v) * d.r⁻¹) * d.r := by group
      _ = 1 := by rw [e']; group
  have hx2 : IsPGroup 2 (zpowers (θ ⟨d.r * v * d.r⁻¹, hrV v hv⟩)) := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hxk)
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hxN : zpowers (θ ⟨d.r * v * d.r⁻¹, hrV v hv⟩) ≤ normalizer (Qb : Set (H ⧸ O)) := by
    rw [zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun y hy => ?_)
    obtain ⟨c, hc, rfl⟩ := hmemQb y hy
    exact (hcomm c hc).symm
  have hDE : D = CFSG.layer (H ⧸ O) := hout.1.2.2.2.1
  rcases hout.1.2.2.2.2.2.1 with ⟨⟨hDs, -⟩, -⟩ | ⟨⟨D₁, D₂, -, -, -, -, -, -, -, -, -, -, -, -, ψ,
    hψ, -⟩, -⟩
  ·
    have hEs : IsSimpleGroup (CFSG.layer (H ⧸ O)) := hDE ▸ hDs
    obtain ⟨hlie, -⟩ := hout.2 hEs
    obtain ⟨K', _, _, hK', ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hlie
    have : CharP K' 2 := finite_field_prime_power_characteristic Nat.prime_two
      (by have := hd.two_le; omega) hK'
    set W : Subgroup (H ⧸ O) := zpowers (θ ⟨d.r * v * d.r⁻¹, hrV v hv⟩) ⊔ Qb with hW
    have hWD : W ≤ D := sup_le (zpowers_le.2 hvD) (hQbJ.trans hJD)
    have hW2 : IsPGroup 2 W := IsPGroup.to_sup_of_normal_right' hx2 hQb2 hxN
    obtain ⟨S₀, hS₀⟩ := (hW2.of_equiv (subgroupOfEquivOfLe hWD).symm).exists_le_sylow
    set S : Subgroup (H ⧸ O) := (S₀ : Subgroup D).map D.subtype with hS
    have hWS : W ≤ S := fun y hy => ⟨⟨y, hWD hy⟩, hS₀ (mem_subgroupOf.2 hy), rfl⟩
    have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S (CFSG.layer (H ⧸ O)) := by
      rw [← hDE]
      exact ⟨S₀, rfl⟩
    obtain ⟨F⟩ := LinearThree.exists_frame e hSyl
    obtain ⟨c₁, hc₁, c₂, hc₂, hne⟩ := hd.exists_not_comm_C₅
    obtain ⟨p, hp, hpx⟩ := F.exists_eq_of_mem_V (hWS (mem_sup_left (mem_zpowers _)))
    obtain ⟨p₁, hp₁, hp₁x⟩ := F.exists_eq_of_mem_V (hWS (mem_sup_right (hcQ c₁ hc₁)))
    obtain ⟨p₂, hp₂, hp₂x⟩ := F.exists_eq_of_mem_V (hWS (mem_sup_right (hcQ c₂ hc₂)))
    have hpq : ∀ (q : LinearFlag.projectiveSL 3 K') (c : G) (hc : c ∈ C₅),
        F.φ q = θ ⟨d.r * c * d.r⁻¹, hN₂H (hrC c hc)⟩ → p * q = q * p := by
      intro q c hc hq
      apply F.injective
      rw [map_mul, map_mul, hpx, hq]
      exact hcomm c hc
    have h12 : p₁ * p₂ ≠ p₂ * p₁ := by
      intro e12
      apply hne
      refine hinjC c₁ hc₁ c₂ hc₂ ?_
      rw [← hp₁x, ← hp₂x, ← map_mul, ← map_mul, e12]
    rw [← LinearThree.map_top_unipEmb] at hp hp₁ hp₂
    obtain ⟨u, -, hu⟩ := hp
    obtain ⟨u₁, -, hu₁⟩ := hp₁
    obtain ⟨u₂, -, hu₂⟩ := hp₂
    have hinjU := LinearThree.unipEmb_injective (K := K')
    have hu1 : u * u₁ = u₁ * u := hinjU (by
      rw [map_mul, map_mul, hu, hu₁]
      exact hpq p₁ c₁ hc₁ hp₁x)
    have hu2 : u * u₂ = u₂ * u := hinjU (by
      rw [map_mul, map_mul, hu, hu₂]
      exact hpq p₂ c₂ hc₂ hp₂x)
    have hu12 : u₁ * u₂ ≠ u₂ * u₁ := fun e12 => h12 (by
      rw [← hu₁, ← hu₂, ← map_mul, ← map_mul, e12])
    have huu := mul_self_eq_one_of_commute_unipAll hu1 hu2 hu12
    calc θ ⟨d.r * v * d.r⁻¹, hrV v hv⟩ * θ ⟨d.r * v * d.r⁻¹, hrV v hv⟩ = F.φ p * F.φ p := by
          rw [hpx]
      _ = F.φ (LinearThree.unipEmb K' (u * u)) := by rw [map_mul, map_mul, hu]
      _ = 1 := by rw [huu, map_one, map_one]
  ·
    have hsq2 : ∀ a : Jb, (∀ c (hc : c ∈ C₅), (a : H ⧸ O) *
        θ ⟨d.r * c * d.r⁻¹, hN₂H (hrC c hc)⟩ = θ ⟨d.r * c * d.r⁻¹, hN₂H (hrC c hc)⟩ * a) →
        a ^ 2 ^ k = 1 → a * a = 1 := by
      intro a ha hak
      have hak' : (a : H ⧸ O) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hak
      have ha2 : IsPGroup 2 (zpowers (a : H ⧸ O)) := by
        obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hak')
        exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
      have haN : zpowers (a : H ⧸ O) ≤ normalizer (Qb : Set (H ⧸ O)) := by
        rw [zpowers_le]
        refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun y hy => ?_)
        obtain ⟨c, hc, rfl⟩ := hmemQb y hy
        exact (ha c hc).symm
      have hsup2 := IsPGroup.to_sup_of_normal_right' ha2 hQb2 haN
      have hle := d.card_le_of_le_image_N₂ (sup_le (zpowers_le.2 a.2) hQbJ) hsup2
      have heq : Qb = zpowers (a : H ⧸ O) ⊔ Qb :=
        Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hcardQb]; exact hle)
      have haQ : (a : H ⧸ O) ∈ Qb := heq ▸ mem_sup_left (mem_zpowers _)
      obtain ⟨c₀, hc₀, hac⟩ := hmemQb _ haQ
      have hc₀Z : c₀ ∈ d.Zp := hd.mem_Zp_of_comm_C₅ hc₀ fun c hc =>
        hinjC c₀ hc₀ c hc (by rw [← hac]; exact ha c hc)
      have hc₀2 : c₀ * c₀ = 1 := d.A₁_comm_sq.2 c₀ (d.Zp_le_A₁ hc₀Z)
      apply Subtype.ext
      rw [coe_mul, hac, ← map_mul, coe_one]
      have e1 : (⟨d.r * c₀ * d.r⁻¹, hN₂H (hrC c₀ hc₀)⟩ : H) *
          ⟨d.r * c₀ * d.r⁻¹, hN₂H (hrC c₀ hc₀)⟩ = 1 := by
        apply Subtype.ext
        simp only [coe_mul, coe_one]
        calc d.r * c₀ * d.r⁻¹ * (d.r * c₀ * d.r⁻¹) = d.r * (c₀ * c₀) * d.r⁻¹ := by group
          _ = 1 := by rw [hc₀2, mul_one, mul_inv_cancel]
      rw [e1, map_one]
    set xt : D := ⟨θ ⟨d.r * v * d.r⁻¹, hrV v hv⟩, hvD⟩ with hxt
    have hxt2 : xt ^ 2 ^ k = 1 := Subtype.ext (by simpa using hxk)
    have hψc : ∀ c (hc : c ∈ C₅), ψ ⟨_, hJD (hcJ c hc)⟩ =
        (⟨_, hcJ c hc⟩, ⟨_, hcJ c hc⟩) := fun c hc => hψ _ (hcJ c hc) (hJD (hcJ c hc))
    have hcommψ : ∀ c (hc : c ∈ C₅), ψ xt * ψ ⟨_, hJD (hcJ c hc)⟩ =
        ψ ⟨_, hJD (hcJ c hc)⟩ * ψ xt := by
      intro c hc
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm c hc)
    have h1 : (ψ xt).1 * (ψ xt).1 = 1 := hsq2 (ψ xt).1 (fun c hc => by
      have := congrArg (fun q => ((q.1 : Jb) : H ⧸ O)) (hcommψ c hc)
      simpa [hψc c hc] using this)
      (by rw [← Prod.pow_fst, ← map_pow, hxt2, map_one, Prod.fst_one])
    have h2 : (ψ xt).2 * (ψ xt).2 = 1 := hsq2 (ψ xt).2 (fun c hc => by
      have := congrArg (fun q => ((q.2 : Jb) : H ⧸ O)) (hcommψ c hc)
      simpa [hψc c hc] using this)
      (by rw [← Prod.pow_snd, ← map_pow, hxt2, map_one, Prod.snd_one])
    have hψsq : ψ (xt * xt) = 1 := by
      rw [map_mul]
      exact Prod.ext h1 h2
    have hxx : xt * xt = 1 := ψ.injective (by rw [hψsq, map_one])
    simpa using congrArg Subtype.val hxx

theorem Hyp.comm_of_mem_V (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {x y : G}
    (hx : x ∈ d.V) (hy : y ∈ d.V) : x * y = y * x := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hd.mul_self_eq_one_of_mem_V hGMS hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hd.mul_self_eq_one_of_mem_V hGMS hy)
  have hxy : (x * y)⁻¹ = x * y :=
    inv_eq_of_mul_eq_one_right (hd.mul_self_eq_one_of_mem_V hGMS (mul_mem hx hy))
  rw [← hxy, mul_inv_rev, hx', hy']

theorem Hyp.isElementaryAbelian_V (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    CFSG.IsElementaryAbelian 2 d.V :=
  isElementaryAbelian_of_forall (fun _ hx _ hy => hd.comm_of_mem_V hGMS hx hy)
    fun _ hx => hd.mul_self_eq_one_of_mem_V hGMS hx

theorem Hyp.eq_V_of_abelian (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {A : Subgroup G} (hA : A ≤ d.V ⊔ zpowers d.t) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAcard : Nat.card A = (2 ^ f) ^ 2) : A = d.V := by
  rw [← hd.CB₄I₃_eq] at hA
  have hidx : d.V.relIndex d.CB₄I₃ = 2 := by
    have e := relIndex_mul_card d.V d.CB₄I₃
    rw [inf_eq_left.2 hd.V_le_CB₄I₃, hd.card_V, hd.card_CB₄I₃] at e
    exact Nat.eq_of_mul_eq_mul_right (by positivity) e
  by_contra hne
  obtain ⟨a, haA, haV⟩ := IsConcreteLE.not_le_iff_exists.1 fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hAcard, hd.card_V]))
  have htV : d.t⁻¹ ∉ d.V := fun h => hd.t_not_mem_V (by simpa using inv_mem h)
  have hvV : a * d.t⁻¹ ∈ d.V := by
    have hidx' : (d.V.subgroupOf d.CB₄I₃).index = 2 := hidx
    have := (mul_mem_iff_of_index_two hidx' (a := ⟨a, hA haA⟩)
      (b := ⟨d.t⁻¹, inv_mem hd.t_mem_CB₄I₃⟩)).2
      (iff_of_false (by rwa [mem_subgroupOf]) (by rwa [mem_subgroupOf]))
    exact mem_subgroupOf.1 this
  have hZ : d.V ⊓ A ≤ d.Zp := by
    intro w hw
    obtain ⟨hwV, hwA⟩ := Subgroup.mem_inf.1 hw
    rw [← hd.V_inf_centralizer_t]
    refine Subgroup.mem_inf.2 ⟨hwV, mem_centralizer_singleton_iff.2 ?_⟩
    have e1 := hAc w hwA a haA
    have e2 := hd.comm_of_mem_V hGMS hwV hvV
    have e3 : a * (w * d.t⁻¹) = a * (d.t⁻¹ * w) := by
      calc a * (w * d.t⁻¹) = w * a * d.t⁻¹ := by rw [e1]; group
        _ = w * (a * d.t⁻¹) := by group
        _ = a * d.t⁻¹ * w := e2
        _ = a * (d.t⁻¹ * w) := by group
    have e4 : w * d.t⁻¹ = d.t⁻¹ * w := mul_left_cancel e3
    calc w * d.t = d.t * (d.t⁻¹ * w) * d.t := by group
      _ = d.t * (w * d.t⁻¹) * d.t := by rw [e4]
      _ = d.t * w := by group
  have hcardI : Nat.card (d.V ⊓ A : Subgroup G) ≤ 2 ^ f := by
    rw [← d.card_Zp]
    exact card_le_of_le hZ
  have hle : d.V.relIndex A ≤ 2 := hidx ▸ relIndex_le_of_le_right hA (by rw [hidx]; norm_num)
  have e := relIndex_mul_card d.V A
  rw [hAcard] at e
  have h1 : (2 ^ f) ^ 2 ≤ 2 * 2 ^ f := e ▸ Nat.mul_le_mul hle hcardI
  have h4 := hd.four_le
  nlinarith

theorem Hyp.normalizer_ZtP_le_normalizer_V (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) : normalizer (d.ZtP : Set G) ≤ normalizer (d.V : Set G) := by
  intro g hg
  refine mem_normalizer_of_map_conj_eq (hd.eq_V_of_abelian hGMS ?_ ?_ ?_)
  · rw [← hd.CB₄I₃_eq, ← map_conj_eq_of_mem_normalizer (hd.normalizer_ZtP_le_normalizer_CB₄I₃ hg)]
    exact map_mono hd.V_le_CB₄I₃
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hd.comm_of_mem_V hGMS hx hy]
  · rw [card_map_of_injective (MulAut.conj g).injective, hd.card_V]

theorem Hyp.exists_crossedHom_V_normalizer (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) :
    ∃ ψ : d.V →* d.Zp, Function.Surjective ψ ∧ ψ.ker = d.Zp.subgroupOf d.V ∧
      (∀ v : d.V, (ψ v : G) = (v : G)⁻¹ * d.t * v * d.t) ∧
      ∀ c ∈ normalizer (d.Zp : Set G) ⊓ centralizer ({d.t} : Set G), ∀ v : d.V,
        ∃ hv : c * v * c⁻¹ ∈ d.V, (ψ ⟨c * v * c⁻¹, hv⟩ : G) = c * ψ v * c⁻¹ := by
  obtain ⟨ψ, hsurj, hker, hψ, -⟩ := hd.exists_crossedHom_V
  refine ⟨ψ, hsurj, hker, hψ, fun c hc v => ?_⟩
  have hcN : c ∈ normalizer (d.ZtP : Set G) := (hd.normalizer_Zp_inf ▸ hc).1
  refine ⟨(mem_normalizer_iff.1 (hd.normalizer_ZtP_le_normalizer_V hGMS hcN) v).1 v.2, ?_⟩
  rw [hψ, hψ]
  exact CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj (mem_centralizer_singleton_iff.1 hc.2)

theorem Hyp.sec3_3_one (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    CFSG.IsElementaryAbelian 2 d.V ∧ Nat.card d.V = (2 ^ f) ^ 2 ∧ d.Zp ≤ d.V ∧
      d.V ≤ normalizer (d.ZtP : Set G) ∧ normalizer (d.ZtP : Set G) ≤ normalizer (d.V : Set G) ∧
      d.V ≤ centralizer (d.P : Set G) ∧ d.B₄ = d.V ⊔ d.B₂ ∧ d.V ⊓ d.B₂ = d.Zp ∧
      ∃ ψ : d.V →* d.Zp, Function.Surjective ψ ∧ ψ.ker = d.Zp.subgroupOf d.V ∧
        (∀ v : d.V, (ψ v : G) = (v : G)⁻¹ * d.t * v * d.t) ∧
        ∀ c ∈ normalizer (d.Zp : Set G) ⊓ centralizer ({d.t} : Set G), ∀ v : d.V,
          ∃ hv : c * v * c⁻¹ ∈ d.V, (ψ ⟨c * v * c⁻¹, hv⟩ : G) = c * ψ v * c⁻¹ :=
  ⟨hd.isElementaryAbelian_V hGMS, hd.card_V, hd.Zp_le_V,
    (hd.V_le_CB₄I₃.trans d.CB₄I₃_le).trans d.B₄_le, hd.normalizer_ZtP_le_normalizer_V hGMS,
    hd.V_le_CB₄I₃.trans hd.CB₄I₃_le_centralizer_P, hd.B₄_eq_V_sup_B₂, hd.V_inf_B₂,
    hd.exists_crossedHom_V_normalizer hGMS⟩

end Data

end CFSG.LocalAnalysis.EvenBN.U5
