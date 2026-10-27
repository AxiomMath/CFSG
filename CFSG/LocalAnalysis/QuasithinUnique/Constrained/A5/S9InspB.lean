module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9InspA
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableBender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableL3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableMathieu
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TablePSL3Cover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TablePSL42
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableSp4

public section

namespace CFSG.QuasithinUnique.A5.Insp

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.Id2519

theorem k32AutExcl_proved
    : K32AutExcl :=
  k32AutExcl_of_families k32ExclBender_proved k32ExclPSL3_proved k32ExclPSp4_proved
    (k32ExclPSL3Cover_of_bound fun _ _ _ _ hF => k32ZBound2_l3_four hF) k32ExclPSL2p_proved
    k32ExclM22_proved k32ExclM22Cover_proved k32ExclM23_proved k32ExclPSL42_proved

theorem kInEightT_of_datum
    {K : Type} [Group K] [Finite K] (hq : CFSG.IsQuasisimple K)
    (hty : K32ListedType K)
    (hdat : ∃ X P R A' V' : Subgroup (MulAut K), K32Datum K X P R A' V') : KInEightT K := by
  by_contra h8
  obtain ⟨X, P, R, A', V', hd⟩ := hdat
  exact k32AutExcl_proved K hq hty h8 X P R A' V' hd

section Cover

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {z u : G} {A V K : Subgroup G}

omit [Finite G] in
@[expose] def centerG (K : Subgroup G) : Subgroup G := (Subgroup.center ↥K).map K.subtype

omit [Finite G] in
theorem mem_centerG {K : Subgroup G} {x : G} :
    x ∈ centerG K ↔ x ∈ K ∧ ∀ k ∈ K, x * k = k * x := by
  constructor
  · intro hx
    unfold centerG at hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨c.2, fun k hk => ?_⟩
    have := Subgroup.mem_center_iff.mp hc ⟨k, hk⟩
    exact congrArg Subtype.val this.symm
  · rintro ⟨hxK, hx⟩
    unfold centerG
    refine Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, Subgroup.mem_center_iff.mpr fun g => ?_, rfl⟩
    exact Subtype.ext (hx g g.2).symm

omit [Finite G] in
theorem le_normalizer_centerG {K : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (centerG K : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (K : Set G), ∀ x ∈ centerG K, g * x * g⁻¹ ∈ centerG K := by
    intro g hg x hx
    obtain ⟨hxK, hx⟩ := mem_centerG.mp hx
    refine mem_centerG.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxK, fun k hk => ?_⟩
    have hk' : g⁻¹ * k * g ∈ K := by
      have hg' : g⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
        (Subgroup.normalizer (K : Set G)).inv_mem hg
      have := (Subgroup.mem_normalizer_iff.mp hg' k).mp hk
      simpa using this
    have hc := hx _ hk'
    calc g * x * g⁻¹ * k = g * (x * (g⁻¹ * k * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * k * g) * x) * g⁻¹ := by rw [hc]
      _ = k * (g * x * g⁻¹) := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have := key g⁻¹ ((Subgroup.normalizer (K : Set G)).inv_mem hg) _ hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at this

theorem false_of_centerG_card_three (cfg : A5Cfg G T M H S L) (D : U9Data T M H S L z u A V)
    (hK : IsComponentIn K (centralizerElem u)) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hZ3 : Nat.card ↥(centerG K) = 3) : False := by
  classical
  have hKG : K ≤ centralizerElem u := hK.1
  have hAZ : A ≤ Subgroup.normalizer (centerG K : Set G) := fun a ha =>
    le_normalizer_centerG (hAK ha)
  set ρ := k32ActHom (centerG K) A hAZ with hρ
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZcyc : IsCyclic ↥(centerG K) := isCyclic_of_prime_card hZ3
  have hfin : Finite (MulAut ↥(centerG K)) :=
    Finite.of_injective (fun f : MulAut ↥(centerG K) => (f : ↥(centerG K) → ↥(centerG K)))
      DFunLike.coe_injective
  have hMA : Nat.card (MulAut ↥(centerG K)) = 2 := by
    rw [IsCyclic.card_mulAut, hZ3, Nat.totient_prime Nat.prime_three]
  have hlt : Nat.card (MulAut ↥(centerG K)) < Nat.card ↥A := by
    rw [hMA, D.hA.card_L]
    norm_num
  have hninj : ¬ Function.Injective ρ := fun hinj =>
    absurd (Nat.card_le_card_of_injective ρ hinj) (not_le.mpr hlt)
  obtain ⟨a, b, hρab, hab⟩ : ∃ a b : ↥A, ρ a = ρ b ∧ a ≠ b := by
    by_contra hcon
    push Not at hcon
    exact hninj fun a b h => hcon a b h
  have hne : A ⊓ Subgroup.centralizer (centerG K : Set G) ≠ ⊥ := by
    intro hbot
    have hw1 : ρ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hρab]; group
    have hwc : ((a⁻¹ * b : ↥A) : G) ∈ Subgroup.centralizer (centerG K : Set G) :=
      (k32ActHom_eq_one_iff (centerG K) A hAZ (a⁻¹ * b)).mp hw1
    have hmem : ((a⁻¹ * b : ↥A) : G) ∈ A ⊓ Subgroup.centralizer (centerG K : Set G) :=
      ⟨(a⁻¹ * b).2, hwc⟩
    rw [hbot] at hmem
    have : a⁻¹ * b = 1 := Subtype.ext (Subgroup.mem_bot.mp hmem)
    exact hab (by
      calc a = a * (a⁻¹ * b) := by rw [this]; group
        _ = b := by group)
  have hV : V ≤ A ⊓ Subgroup.centralizer (centerG K : Set G) :=
    k32_le_of_normal_ne_bot D.hA inf_le_left (k32_le_normalizer_inf_centralizer hAZ) hne
  have huzC : u * z ∈ Subgroup.centralizer (centerG K : Set G) := (hV D.uz_mem).2
  have hzZ : ∀ y ∈ centerG K, z * y = y * z := by
    intro y hy
    have hyK : y ∈ K := (mem_centerG.mp hy).1
    have h1 : y * (u * z) = (u * z) * y := Subgroup.mem_centralizer_iff.mp huzC y hy
    have hyu : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp (hKG hyK)
    have h2 : u * (y * z) = u * (z * y) := by
      calc u * (y * z) = (u * y) * z := by group
        _ = (y * u) * z := by rw [hyu]
        _ = y * (u * z) := by group
        _ = (u * z) * y := h1
        _ = u * (z * y) := by group
    exact (mul_left_cancel h2).symm
  obtain ⟨y, hy1⟩ : ∃ y : ↥(centerG K), y ≠ 1 := by
    have hZne : centerG K ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hZ3
      omega
    exact Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hy3 : y ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥(centerG K)) (x := y)
    rwa [hZ3] at this
  have hyTu : (y : G) ∈ T ⊓ centralizerElem u :=
    mem_Tu_of_commute D (hKG (mem_centerG.mp y.2).1) (hzZ y y.2)
  obtain ⟨n, hn⟩ := Tu_isPGroup cfg (u := u) ⟨(y : G), hyTu⟩
  have hn' : (y : G) ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hy3' : (y : G) ^ 3 = 1 := congrArg Subtype.val hy3
  have h1 : orderOf (y : G) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
  have h2 : orderOf (y : G) ∣ 3 := orderOf_dvd_of_pow_eq_one hy3'
  have hord : orderOf (y : G) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left n (by norm_num)) h1 h2
  exact hy1 (Subtype.ext (orderOf_eq_one_iff.mp hord))

end Cover

end CFSG.QuasithinUnique.A5.Insp
