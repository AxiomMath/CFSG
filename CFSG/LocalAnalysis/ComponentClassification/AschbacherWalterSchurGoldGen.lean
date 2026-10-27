module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingBender
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
public import CFSG.LocalAnalysis.QuasithinUnique.ComponentNormalization
public import CFSG.Walter.AStar.Basic

public section

namespace CFSG.ComponentClassification.WalterSchur

open CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTheorem3

section Abstract

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_zpowers_of_mul_self {s : G} (hs : s * s = 1) :
    IsPGroup 2 (Subgroup.zpowers s) :=
  IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hs))

theorem exists_smul_eq_of_le (M : Subgroup G) {Q R : Sylow 2 G} (hQ : (Q : Subgroup G) ≤ M)
    (hR : (R : Subgroup G) ≤ M) : ∃ m ∈ M, m • Q = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M (Q.subtype hQ) (R.subtype hR)
  rw [Sylow.smul_subtype] at hm
  exact ⟨m, m.2, Sylow.subtype_injective hm⟩

theorem exists_conj_mem_of_le (M : Subgroup G) {Q : Sylow 2 G} (hQ : (Q : Subgroup G) ≤ M)
    {s : G} (hs : s ∈ M) (hs2 : s * s = 1) : ∃ m ∈ M, m⁻¹ * s * m ∈ (Q : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set s' : M := ⟨s, hs⟩
  have hs'2 : IsPGroup 2 (Subgroup.zpowers s') :=
    isPGroup_zpowers_of_mul_self (Subtype.ext hs2)
  obtain ⟨R, hR⟩ := hs'2.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M (Q.subtype hQ) R
  have hsR : s' ∈ (R : Subgroup M) := hR (Subgroup.mem_zpowers s')
  rw [← hm, Sylow.smul_subtype, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hsR
  refine ⟨m, m.2, ?_⟩
  rw [Subgroup.smul_def, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hsR
  obtain ⟨q, hq, hqs⟩ := hsR
  rw [MulAut.smul_def, MulAut.conj_apply] at hqs
  rw [show (m : G)⁻¹ * s * m = q by rw [show s = (s' : G) from rfl, ← hqs]; group]
  exact hq

theorem centralizers_eq_top_or_isBenderGroup [IsSimpleGroup G] (Q : Sylow 2 G)
    (hQ : IsMulCommutative (Q : Subgroup G)) {a b : G} (ha : a ∈ (Q : Subgroup G))
    (hb : b ∈ (Q : Subgroup G)) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hab : a ≠ b) :
    (⨆ z : {z : G // z ∈ (Q : Subgroup G) ∧ z ^ 2 = 1 ∧ z ≠ 1},
      Subgroup.centralizer {(z : G)}) = ⊤ ∨ fusionIsBenderGroup G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := {z : G // z ∈ (Q : Subgroup G) ∧ z ^ 2 = 1 ∧ z ≠ 1}
  set M : Subgroup G := ⨆ z : I, Subgroup.centralizer {(z : G)} with hMdef
  set N := Subgroup.normalizer ((Q : Subgroup G) : Set G) with hNdef
  set M₁ := M ⊔ N with hM₁def
  have hinvI : ∀ z : G, orderOf z = 2 → z ∈ (Q : Subgroup G) → z ∈ M := by
    intro z hz hzQ
    have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have hz1 : z ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hz
      omega
    exact (le_iSup (fun z : I => Subgroup.centralizer {(z : G)}) ⟨z, hzQ, hz2, hz1⟩)
      (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hCM : ∀ z : G, z ∈ (Q : Subgroup G) → z ^ 2 = 1 → z ≠ 1 →
      Subgroup.centralizer {z} ≤ M := fun z hzQ hz2 hz1 =>
    le_iSup (fun z : I => Subgroup.centralizer {(z : G)}) ⟨z, hzQ, hz2, hz1⟩
  have hmap : ∀ n ∈ N, M.map (MulAut.conj n).toMonoidHom ≤ M := by
    intro n hn
    rw [hMdef, Subgroup.map_iSup]
    refine iSup_le fun z => ?_
    rintro _ ⟨x, hx, rfl⟩
    have hzQ : n * z * n⁻¹ ∈ (Q : Subgroup G) := (Subgroup.mem_normalizer_iff.mp hn z).mp z.2.1
    have hz2 : (n * z * n⁻¹) ^ 2 = 1 := by
      rw [sq, show n * (z : G) * n⁻¹ * (n * z * n⁻¹) = n * (z * z) * n⁻¹ by group, ← sq,
        z.2.2.1, mul_one, mul_inv_cancel]
    have hz1 : n * z * n⁻¹ ≠ 1 := by
      intro h
      apply z.2.2.2
      rw [mul_inv_eq_one, mul_eq_left] at h
      exact h
    refine hCM _ hzQ hz2 hz1 (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
    have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    change n * x * n⁻¹ * (n * z * n⁻¹) = n * z * n⁻¹ * (n * x * n⁻¹)
    calc n * x * n⁻¹ * (n * z * n⁻¹) = n * (x * z) * n⁻¹ := by group
      _ = n * (z * x) * n⁻¹ := by rw [hxz]
      _ = n * z * n⁻¹ * (n * x * n⁻¹) := by group
  have hNM : N ≤ Subgroup.normalizer (M : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hmap n hn ⟨h, hh, rfl⟩
    · intro hh
      have h' := hmap n⁻¹ (Subgroup.inv_mem _ hn) ⟨_, hh, rfl⟩
      simpa [mul_assoc] using h'
  have haM : a ∈ M := hinvI a ha2 ha
  by_cases htop : M₁ = ⊤
  ·
    left
    have hMn : M.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
      exact sup_le Subgroup.le_normalizer hNM
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h | h
    · exfalso
      rw [h, Subgroup.mem_bot] at haM
      rw [haM, orderOf_one] at ha2
      omega
    · exact h
  right
  have hQM₁ : (Q : Subgroup G) ≤ M₁ := le_sup_of_le_right Subgroup.le_normalizer
  have hab' : Commute a b := hQ.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩ |> congrArg Subtype.val
  have hall : Walter.HasAbelianSylowTwo G := Walter.hasAbelianSylowTwo_of_sylow Q hQ
  have hKC : ∀ s ∈ M₁, s * s = 1 → s ≠ 1 → Subgroup.centralizer {s} ≤ M₁ := by
    intro s hs hs2 hs1
    obtain ⟨m, hm, hmQ⟩ := exists_conj_mem_of_le M₁ hQM₁ hs hs2
    have hz2 : (m⁻¹ * s * m) ^ 2 = 1 := by
      rw [sq, show m⁻¹ * s * m * (m⁻¹ * s * m) = m⁻¹ * (s * s) * m by group, hs2, mul_one,
        inv_mul_cancel]
    have hz1 : m⁻¹ * s * m ≠ 1 := by
      intro h
      apply hs1
      have h' := congrArg (fun w => m * w * m⁻¹) h
      simpa [mul_assoc] using h'
    have hC := hCM _ hmQ hz2 hz1
    intro x hx
    have hxs : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    have hy : m⁻¹ * x * m ∈ Subgroup.centralizer {m⁻¹ * s * m} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc m⁻¹ * x * m * (m⁻¹ * s * m) = m⁻¹ * (x * s) * m := by group
        _ = m⁻¹ * (s * x) * m := by rw [hxs]
        _ = m⁻¹ * s * m * (m⁻¹ * x * m) := by group
    have hyM : m⁻¹ * x * m ∈ M₁ := (le_sup_left : M ≤ M ⊔ N) (hC hy)
    have hx' : x = m * (m⁻¹ * x * m) * m⁻¹ := by group
    rw [hx']
    exact M₁.mul_mem (M₁.mul_mem hm hyM) (M₁.inv_mem hm)
  have hSylC : ∀ s : G, s * s = 1 → ∃ R : Sylow 2 G, (R : Subgroup G) ≤ Subgroup.centralizer {s} ∧
      s ∈ (R : Subgroup G) := by
    intro s hs2
    have hs2' : IsPGroup 2 (Subgroup.zpowers s) := isPGroup_zpowers_of_mul_self hs2
    obtain ⟨R, hR⟩ := hs2'.exists_le_sylow
    have hsR : s ∈ (R : Subgroup G) := hR (Subgroup.mem_zpowers s)
    refine ⟨R, fun r hr => ?_, hsR⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val ((hall R).is_comm.comm ⟨r, hr⟩ ⟨s, hsR⟩)
  have hSE : fusionStronglyEmbedded M₁ := by
    refine ⟨htop, ?_, ?_⟩
    ·
      have h2Q : 2 ∣ Nat.card (Q : Subgroup G) := by
        have h := orderOf_dvd_natCard (⟨a, ha⟩ : (Q : Subgroup G))
        rwa [Subgroup.orderOf_mk, ha2] at h
      exact even_iff_two_dvd.mpr (h2Q.trans (Subgroup.card_dvd_of_le hQM₁))
    · intro g hg
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := (M₁ ⊓ M₁.map
        (MulAut.conj g⁻¹).toMonoidHom : Subgroup G)) 2 (even_iff_two_dvd.mp hev)
      have htM : (t : G) ∈ M₁ := (Subgroup.mem_inf.mp t.2).1
      obtain ⟨u, huM, hut⟩ := (Subgroup.mem_inf.mp t.2).2
      have ht2 : (t : G) * t = 1 := by
        have h := pow_orderOf_eq_one t
        rw [ht, sq] at h
        exact congrArg Subtype.val h
      have ht1 : (t : G) ≠ 1 := by
        intro h
        have h1 : t = 1 := Subtype.ext h
        rw [h1, orderOf_one] at ht
        omega
      have hut' : u = g * t * g⁻¹ := by
        have h : g⁻¹ * u * g⁻¹⁻¹ = t := hut
        rw [inv_inv] at h
        rw [← h]
        group
      have hu2 : u * u = 1 := by
        rw [hut', show g * (t : G) * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ht2,
          mul_one, mul_inv_cancel]
      have hu1 : u ≠ 1 := by
        intro h
        apply ht1
        rw [hut', mul_inv_eq_one, mul_eq_left] at h
        exact h
      have hCt := hKC _ htM ht2 ht1
      have hCu := hKC _ huM hu2 hu1
      obtain ⟨R, hRC, -⟩ := hSylC _ ht2
      have hRM : (R : Subgroup G) ≤ M₁ := hRC.trans hCt
      have hgRM : ((g • R : Sylow 2 G) : Subgroup G) ≤ M₁ := by
        intro x hx
        rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx
        obtain ⟨r, hr, rfl⟩ := hx
        apply hCu
        rw [Subgroup.mem_centralizer_singleton_iff, MulAut.smul_def, MulAut.conj_apply, hut']
        have hrt : r * t = t * r := Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)
        calc g * r * g⁻¹ * (g * t * g⁻¹) = g * (r * t) * g⁻¹ := by group
          _ = g * (t * r) * g⁻¹ := by rw [hrt]
          _ = g * t * g⁻¹ * (g * r * g⁻¹) := by group
      obtain ⟨m, hm, hmR⟩ := exists_smul_eq_of_le M₁ hQM₁ hRM
      obtain ⟨m', hm', hm'R⟩ := exists_smul_eq_of_le M₁ hQM₁ hgRM
      have hnorm : m'⁻¹ * g * m ∈ N := by
        have h : (m'⁻¹ * g * m) • Q = Q := by
          rw [mul_smul, mul_smul, hmR, ← hm'R, inv_smul_smul]
        exact Sylow.smul_eq_iff_mem_normalizer.mp h
      apply hg
      have hgm : g = m' * (m'⁻¹ * g * m) * m⁻¹ := by group
      rw [hgm]
      exact M₁.mul_mem (M₁.mul_mem hm' ((le_sup_right : N ≤ M ⊔ N) hnorm)) (M₁.inv_mem hm)
  have heven : Even (Nat.card G) := by
    have h2 : 2 ∣ Nat.card G := by
      have h := orderOf_dvd_natCard a
      rwa [ha2] at h
    exact even_iff_two_dvd.mpr h2
  have hO : CFSG.oddCore G = ⊥ := CFSG.QuasithinUnique.oddCore_eq_bot_of_isSimpleGroup_of_even heven
  have hgen : ∀ N' : Subgroup G, N'.Normal → Odd N'.index → N' = ⊤ := by
    intro N' hN' hodd
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N' with h | h
    · exfalso
      rw [h, Subgroup.index_bot] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) heven
    · exact h
  exact AschbacherStrongEmbedding.fusionIsBenderGroup_of_stronglyEmbedded hO hgen hSE ha2 hb2
    hab' hab

end Abstract

section Ambient

variable {Y : Type} [Group Y] [Finite Y] {X P : Subgroup Y}

theorem le_iSup_centralizer_or_isBenderType (hX : IsSimpleGroup X) (hP : IsSylowOf 2 P X)
    (hPc : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p) {a b : Y} (ha : a ∈ P) (hb : b ∈ P)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hab : a ≠ b) :
    (∃ n : ℕ, IsBenderType X n) ∨
    X ≤ ⨆ z : {z : Y // z ∈ P ∧ z ^ 2 = 1 ∧ z ≠ 1}, X ⊓ Subgroup.centralizer {(z : Y)} := by
  obtain ⟨Q, hQ⟩ := hP
  have hPX : P ≤ X := by rw [← hQ]; exact Subgroup.map_subtype_le _
  have hmemQ : ∀ x : X, x ∈ (Q : Subgroup X) ↔ (x : Y) ∈ P := by
    intro x
    rw [← hQ, Subgroup.mem_map]
    exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨y, hy, hyx⟩ => (Subtype.ext hyx : y = x) ▸ hy⟩
  have hQc : IsMulCommutative (Q : Subgroup X) :=
    ⟨⟨fun u v => Subtype.ext (Subtype.ext (hPc _ ((hmemQ _).mp u.2) _ ((hmemQ _).mp v.2)))⟩⟩
  set a' : X := ⟨a, hPX ha⟩
  set b' : X := ⟨b, hPX hb⟩
  have : IsSimpleGroup X := hX
  rcases centralizers_eq_top_or_isBenderGroup Q hQc ((hmemQ a').mpr ha) ((hmemQ b').mpr hb)
      (by rw [Subgroup.orderOf_mk]; exact ha2) (by rw [Subgroup.orderOf_mk]; exact hb2)
      (fun h => hab (congrArg Subtype.val h)) with htop | hB
  · right
    intro x hx
    have hx' : (⟨x, hx⟩ : X) ∈ (⨆ z : {z : X // z ∈ (Q : Subgroup X) ∧ z ^ 2 = 1 ∧ z ≠ 1},
        Subgroup.centralizer {(z : X)}) := htop ▸ Subgroup.mem_top _
    have hle : (⨆ z : {z : X // z ∈ (Q : Subgroup X) ∧ z ^ 2 = 1 ∧ z ≠ 1},
        Subgroup.centralizer {(z : X)}).map X.subtype ≤
        ⨆ z : {z : Y // z ∈ P ∧ z ^ 2 = 1 ∧ z ≠ 1}, X ⊓ Subgroup.centralizer {(z : Y)} := by
      rw [Subgroup.map_iSup]
      refine iSup_le fun z => ?_
      have hzI : ((z : X) : Y) ∈ P ∧ ((z : X) : Y) ^ 2 = 1 ∧ ((z : X) : Y) ≠ 1 :=
        ⟨(hmemQ _).mp z.2.1, by rw [← Subgroup.coe_pow, z.2.2.1, OneMemClass.coe_one],
          fun h => z.2.2.2 (Subtype.ext h)⟩
      refine le_trans ?_ (le_iSup (fun z : {z : Y // z ∈ P ∧ z ^ 2 = 1 ∧ z ≠ 1} =>
        X ⊓ Subgroup.centralizer {(z : Y)}) ⟨_, hzI⟩)
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
    exact hle ⟨⟨x, hx⟩, hx', rfl⟩
  · left
    rcases hB with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · exact ⟨f, Or.inl ⟨hf, ⟨e⟩⟩⟩
    · exact ⟨f, Or.inr (Or.inr ⟨hf, ⟨e⟩⟩)⟩
    · exact ⟨2 * n + 1, Or.inr (Or.inl ⟨n, hn, rfl, ⟨e⟩⟩)⟩

end Ambient

end CFSG.ComponentClassification.WalterSchur
