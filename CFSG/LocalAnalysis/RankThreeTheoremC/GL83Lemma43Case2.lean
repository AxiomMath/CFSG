module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.Open.GLBDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43Case2Y
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem l43_mem_glbPrimeCore_of_mk_eq_one {H : Subgroup G} {r : G} (hr : r ∈ H)
    (h : QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨r, hr⟩ = 1) :
    r ∈ GLBPrimeCore 3 H := by
  have h1 : (⟨r, hr⟩ : H) ∈ primeComplementCore (G := H) 3 := (QuotientGroup.eq_one_iff _).mp h
  rw [← CFSG.AGLEmbedding.glbPrimeCore_subgroupOf] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem m11_conj_mem_sup_of_data
    (hK : CFSG.Open.IsKProper G) (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (hK3 : KFactOutCyclic)
    {P : Sylow 3 G} (hPab : IsMulCommutative (P : Subgroup G)) {M : Subgroup G} (hMtop : M ≠ ⊤)
    (hPM : (P : Subgroup G) ≤ M) {x : G} (hxP : x ∈ (P : Subgroup G)) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1)
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    {K₀ : Subgroup G} (hK₀P : K₀ ≤ (P : Subgroup G)) (hK₀C : K₀ ≤ centralizer ({x} : Set G))
    (hK₀el : IsElemAbelian 3 K₀) (hK₀card : Nat.card K₀ = 9)
    (htrans : ∀ a ∈ K₀, ∀ b ∈ K₀, a ≠ 1 → b ≠ 1 → ∃ n ∈ centralizer ({x} : Set G),
      n ∈ normalizer (K₀ : Set G) ∧ n * a * n⁻¹ = b)
    (hNM : normalizer (K₀ : Set G) ≤ M)
    (hOxM : GLBPrimeCore 3 (centralizer ({x} : Set G)) ≤ M)
    (hCM : M ⊓ centralizer ({x} : Set G) ≤
      normalizer ((K₀ ⊔ GLBPrimeCore 3 (centralizer ({x} : Set G)) : Subgroup G) : Set G)) :
    ∀ m ∈ M, ∀ q ∈ K₀, m * q * m⁻¹ ∈ (P : Subgroup G) ⊔ GLBPrimeCore 3 M := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hxM : x ∈ M := hPM hxP
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hK₀M : K₀ ≤ M := hK₀P.trans hPM
  have hbase := case2Hyp_quotient_of_isKProper hK hPab hMtop hxM hxo hwc
  have hxo' : orderOf (⟨x, hxM⟩ : M) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hxo
  set O : Subgroup M := primeComplementCore (G := M) 3
  set π : M →* M ⧸ O := QuotientGroup.mk' O
  set xb : M ⧸ O := π ⟨x, hxM⟩ with hxb
  have hπc : ∀ a b : M, π (a * b * a⁻¹) = π a * π b * (π a)⁻¹ := fun a b => by
    rw [map_mul, map_mul, map_inv]
  set Z : Subgroup (M ⧸ O) := (K₀.subgroupOf M).map π with hZ
  have hZmem : ∀ z, z ∈ Z ↔ ∃ m : M, (m : G) ∈ K₀ ∧ π m = z := by
    intro z
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, mem_subgroupOf.mp hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, mem_subgroupOf.mpr hm, rfl⟩
  have hZelem : IsElemAbelian 3 Z := by
    have hK₀comm : IsMulCommutative K₀ := hK₀el.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨m₁, hm₁, h₁⟩ := (hZmem a).mp a.2
      obtain ⟨m₂, hm₂, h₂⟩ := (hZmem b).mp b.2
      apply Subtype.ext
      show (a : M ⧸ O) * b = b * a
      rw [← h₁, ← h₂, ← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext (setLike_mul_comm hm₁ hm₂))
    · obtain ⟨m, hm, rfl⟩ := (hZmem z).mp hz
      rw [← map_pow]
      have : m ^ 3 = 1 := Subtype.ext (by simpa using hK₀el.2 (m : G) hm)
      rw [this, map_one]
  have hZcard9 : Nat.card Z = 9 := by
    have hK₀p : IsPGroup 3 (K₀.subgroupOf M) := (elementary_isPGroup 3 K₀ hK₀el).comap_subtype
    rw [hZ, CFSG.AGLEmbedding.card_map_mk_of_isPGroup hp O (primeComplementCore_coprime 3) hK₀p,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK₀M).toEquiv, hK₀card]
  have hZcard : Nat.card Z = 3 ^ 2 := by
    rw [hZcard9]
    norm_num
  have hZc : Z ≤ centralizer ({xb} : Set (M ⧸ O)) := by
    intro z hz
    obtain ⟨m, hm, rfl⟩ := (hZmem z).mp hz
    rw [mem_centralizer_singleton_iff, hxb, ← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (mem_centralizer_singleton_iff.mp (hK₀C hm)))
  set S : Set (M ⧸ O) := {s | s * xb * s⁻¹ = xb ∧ ∀ z ∈ Z, s * z * s⁻¹ ∈ Z}
  have hirr : ∀ D : Subgroup (M ⧸ O), D ≤ Z → (∀ s ∈ S, ∀ d ∈ D, s * d * s⁻¹ ∈ D) →
      D = ⊥ ∨ D = Z := by
    intro D hDZ hDS
    by_cases hD : D = ⊥
    · exact Or.inl hD
    refine Or.inr (le_antisymm hDZ fun z hz => ?_)
    obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hD ((Subgroup.eq_bot_iff_forall D).mpr hcon)
    by_cases hz1 : z = 1
    · rw [hz1]
      exact D.one_mem
    obtain ⟨ma, hma, rfl⟩ := (hZmem d).mp (hDZ hdD)
    obtain ⟨mb, hmb, rfl⟩ := (hZmem z).mp hz
    have ha1 : (ma : G) ≠ 1 := fun h => hd1 (by
      have : ma = 1 := Subtype.ext h
      rw [this, map_one])
    have hb1 : (mb : G) ≠ 1 := fun h => hz1 (by
      have : mb = 1 := Subtype.ext h
      rw [this, map_one])
    obtain ⟨n, hnC, hnN, hnab⟩ := htrans _ hma _ hmb ha1 hb1
    have hnM : n ∈ M := hNM hnN
    have hs : π ⟨n, hnM⟩ ∈ S := by
      refine ⟨?_, fun z' hz' => ?_⟩
      · have h1 : n * x = x * n := mem_centralizer_singleton_iff.mp hnC
        rw [hxb, ← hπc]
        exact congrArg π (Subtype.ext (show n * x * n⁻¹ = x by rw [h1, mul_inv_cancel_right]))
      · obtain ⟨m', hm', rfl⟩ := (hZmem z').mp hz'
        have hnm : n * (m' : G) * n⁻¹ ∈ K₀ := (mem_normalizer_iff.mp hnN _).mp hm'
        refine (hZmem _).mpr ⟨⟨n * (m' : G) * n⁻¹,
          M.mul_mem (M.mul_mem hnM m'.2) (M.inv_mem hnM)⟩, hnm, ?_⟩
        exact hπc ⟨n, hnM⟩ m'
    have hconj : π ⟨n, hnM⟩ * π ma * (π ⟨n, hnM⟩)⁻¹ = π mb := by
      rw [← hπc]
      exact congrArg π (Subtype.ext hnab)
    have := hDS _ hs _ hdD
    rwa [hconj] at this
  set Cx : Subgroup G := centralizer ({x} : Set G)
  set Ox : Subgroup G := GLBPrimeCore 3 Cx
  set Ob : Subgroup (M ⧸ O) := (Ox.subgroupOf M).map π
  have hObcop : ¬ 3 ∣ Nat.card Ob := by
    intro hdvd
    have h1 : Nat.card Ob ∣ Nat.card (Ox.subgroupOf M) :=
      Subgroup.card_dvd_of_surjective (f := π.subgroupMap (Ox.subgroupOf M))
        (π.subgroupMap_surjective _)
    have h2 : Nat.card (Ox.subgroupOf M) = Nat.card Ox :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOxM).toEquiv
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp (CFSG.AGLEmbedding.glbPrimeCore_coprime 3 Cx)
      (h2 ▸ hdvd.trans h1)
  have hCy : centralizer ({xb} : Set (M ⧸ O)) ≤ ((M ⊓ Cx).subgroupOf M).map π :=
    (centralizer_mk_le_map hp hxo').trans (Subgroup.map_mono fun c
      (hc : c ∈ centralizer ({(⟨x, hxM⟩ : M)} : Set M)) => mem_subgroupOf.mpr
      ⟨c.2, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc))⟩)
  have hnormO : centralizer ({xb} : Set (M ⧸ O)) ≤ normalizer (Ob : Set (M ⧸ O)) :=
    hCy.trans (map_subgroupOf_le_normalizer_map
      (fun c (hc : c ∈ M ⊓ Cx) => CFSG.AGLEmbedding.le_normalizer_glbPrimeCore 3 Cx hc.2) π)
  have hZO : Z ⊔ Ob = ((K₀ ⊔ Ox).subgroupOf M).map π := by
    rw [Subgroup.subgroupOf_sup hK₀M hOxM, Subgroup.map_sup]
  have hnormZO : centralizer ({xb} : Set (M ⧸ O)) ≤
      normalizer ((Z ⊔ Ob : Subgroup (M ⧸ O)) : Set (M ⧸ O)) := by
    rw [hZO]
    exact hCy.trans (map_subgroupOf_le_normalizer_map hCM π)
  have hdata : Case2DataTwo (M ⧸ O) xb Z S Ob :=
    { base := hbase
      isElemAbelian := hZelem
      card_eq := ⟨2, le_rfl, hZcard⟩
      le_centralizer := hZc
      centralizes := fun s hs => hs.1
      normalizes := fun s hs => hs.2
      irreducible := hirr
      coprime := hObcop
      normalizes_O := hnormO
      normalizes_ZO := hnormZO }
  have hZp : Z ≤ CFSG.pCore 3 (M ⧸ O) := hdata.le_pCore hInn hWC hK3
  have hPsyl : IsSylowOf 3 (P : Subgroup G) M := isSylowOf_iff.mpr ⟨hPM, P.isPGroup', fun hdvd =>
    P.not_dvd_index (hdvd.trans (Subgroup.relIndex_dvd_index_of_le hPM))⟩
  obtain ⟨R, hR⟩ : ∃ R : Sylow 3 (M ⧸ O), (R : Subgroup (M ⧸ O)) =
      ((P : Subgroup G).subgroupOf M).map π := by
    obtain ⟨-, hp', hdvd⟩ := isSylowOf_iff.1 (isSylowOf_top_map_mk hPsyl)
    rw [Subgroup.relIndex_top_right] at hdvd
    exact ⟨hp'.toSylow hdvd, IsPGroup.toSylow_coe _ _⟩
  intro m hm q hq
  have hqM : q ∈ M := hK₀M hq
  have hmq : m * q * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm hqM) (M.inv_mem hm)
  have hZq : π ⟨q, hqM⟩ ∈ Z := (hZmem _).mpr ⟨⟨q, hqM⟩, hq, rfl⟩
  have hcj : π ⟨m * q * m⁻¹, hmq⟩ = π ⟨m, hm⟩ * π ⟨q, hqM⟩ * (π ⟨m, hm⟩)⁻¹ :=
    hπc ⟨m, hm⟩ ⟨q, hqM⟩
  have hpc : π ⟨m * q * m⁻¹, hmq⟩ ∈ CFSG.pCore 3 (M ⧸ O) := by
    rw [hcj]
    exact (CFSG.pCore_normal (p := 3) (G := M ⧸ O)).conj_mem _ (hZp hZq) _
  have hpR : π ⟨m * q * m⁻¹, hmq⟩ ∈ (R : Subgroup (M ⧸ O)) :=
    CFSG.pCore_isPGroup.le_sylow_of_normal R hpc
  rw [hR] at hpR
  obtain ⟨p', hp', hp'eq⟩ := hpR
  have hp'P : (p' : G) ∈ (P : Subgroup G) := mem_subgroupOf.mp hp'
  have hr : (p' : G)⁻¹ * (m * q * m⁻¹) ∈ M := M.mul_mem (M.inv_mem p'.2) hmq
  have hker : π ⟨(p' : G)⁻¹ * (m * q * m⁻¹), hr⟩ = 1 := by
    have e : (⟨(p' : G)⁻¹ * (m * q * m⁻¹), hr⟩ : M) = p'⁻¹ * ⟨m * q * m⁻¹, hmq⟩ := rfl
    rw [e, map_mul, map_inv, hp'eq, inv_mul_cancel]
  have hrO := l43_mem_glbPrimeCore_of_mk_eq_one hr hker
  have : m * q * m⁻¹ = (p' : G) * ((p' : G)⁻¹ * (m * q * m⁻¹)) := by group
  rw [this]
  exact Subgroup.mul_mem _ (mem_sup_left hp'P) (mem_sup_right hrO)

theorem m11_normalizer_sup_of_data
    (hK : CFSG.Open.IsKProper G) (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (hK3 : KFactOutCyclic)
    {P : Sylow 3 G} (hPab : IsMulCommutative (P : Subgroup G)) {M : Subgroup G} (hMtop : M ≠ ⊤)
    (hPM : (P : Subgroup G) ≤ M) {x : G} (hxP : x ∈ (P : Subgroup G)) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1)
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    {K₀ : Subgroup G} (hK₀P : K₀ ≤ (P : Subgroup G)) (hK₀C : K₀ ≤ centralizer ({x} : Set G))
    (hK₀el : IsElemAbelian 3 K₀) (hK₀card : Nat.card K₀ = 9)
    (htrans : ∀ a ∈ K₀, ∀ b ∈ K₀, a ≠ 1 → b ≠ 1 → ∃ n ∈ centralizer ({x} : Set G),
      n ∈ normalizer (K₀ : Set G) ∧ n * a * n⁻¹ = b)
    (hNM : normalizer (K₀ : Set G) ≤ M)
    (hOxM : GLBPrimeCore 3 (centralizer ({x} : Set G)) ≤ M)
    (hCM : M ⊓ centralizer ({x} : Set G) ≤
      normalizer ((K₀ ⊔ GLBPrimeCore 3 (centralizer ({x} : Set G)) : Subgroup G) : Set G))
    (hSC : ∀ a ∈ K₀, ∀ g : G, g * a * g⁻¹ ∈ (P : Subgroup G) → g * a * g⁻¹ ∈ K₀) :
    M ≤ normalizer ((K₀ ⊔ GLBPrimeCore 3 M : Subgroup G) : Set G) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hconj := m11_conj_mem_sup_of_data hK hInn hWC hK3 hPab hMtop hPM hxP hx3 hx1 hwc hK₀P hK₀C
    hK₀el hK₀card htrans hNM hOxM hCM
  have hOM : GLBPrimeCore 3 M ≤ M := CFSG.AGLEmbedding.glbPrimeCore_le 3 M
  have hMO : M ≤ normalizer (GLBPrimeCore 3 M : Set G) :=
    CFSG.AGLEmbedding.le_normalizer_glbPrimeCore 3 M
  have hK₀M : K₀ ≤ M := hK₀P.trans hPM
  have hPO : (P : Subgroup G) ≤ normalizer (GLBPrimeCore 3 M : Set G) := hPM.trans hMO
  have hPsylW : IsSylowOf 3 (P : Subgroup G) ((P : Subgroup G) ⊔ GLBPrimeCore 3 M) :=
    isSylowOf_iff.mpr ⟨le_sup_left, P.isPGroup', fun hdvd => P.not_dvd_index
      (hdvd.trans (Subgroup.relIndex_dvd_index_of_le le_sup_left))⟩
  have hK₀p : IsPGroup 3 K₀ := elementary_isPGroup 3 K₀ hK₀el
  have hstar : ∀ m ∈ M, ∀ a ∈ K₀, m * a * m⁻¹ ∈ K₀ ⊔ GLBPrimeCore 3 M := by
    intro m hm a ha
    set O : Subgroup G := GLBPrimeCore 3 M
    set W : Subgroup G := (P : Subgroup G) ⊔ O
    set K₁ : Subgroup G := K₀.map (MulAut.conj m).toMonoidHom
    have hK₁W : K₁ ≤ W := by
      rintro _ ⟨k, hk, rfl⟩
      exact hconj m hm k hk
    have hK₁p : IsPGroup 3 K₁ := hK₀p.map (MulAut.conj m).toMonoidHom
    obtain ⟨Q, hQ⟩ := (hK₁p.comap_subtype (K := W)).exists_le_sylow
    set T : Subgroup G := (Q : Subgroup W).map W.subtype
    have hTsyl : IsSylowOf 3 T W := ⟨Q, rfl⟩
    have hK₁T : K₁ ≤ T := fun y hy => ⟨⟨y, hK₁W hy⟩, hQ hy, rfl⟩
    obtain ⟨k, hkW, hk⟩ := hTsyl.exists_mem_conj hPsylW
    have hkmul : k ∈ ((P : Subgroup G) : Set G) * (O : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (P : Subgroup G) O hPO]
      exact hkW
    obtain ⟨p, hpP, o, hoO, rfl⟩ := hkmul
    have hoy : ∀ y ∈ K₁, o * y * o⁻¹ ∈ (P : Subgroup G) := by
      intro y hy
      have h1 : (p * o)⁻¹ * (p * o * y * (p * o)⁻¹) * (p * o) ∈ T := by
        rw [show (p * o)⁻¹ * (p * o * y * (p * o)⁻¹) * (p * o) = y by group]
        exact hK₁T hy
      have h2 : p * o * y * (p * o)⁻¹ ∈ (P : Subgroup G) := (hk _).mpr h1
      have h3 : o * y * o⁻¹ = p⁻¹ * (p * o * y * (p * o)⁻¹) * p := by group
      rw [h3]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hpP) h2) hpP
    have hg : (o * m) * a * (o * m)⁻¹ ∈ K₀ := by
      refine hSC a ha (o * m) ?_
      have h1 := hoy (m * a * m⁻¹) ⟨a, ha, rfl⟩
      rw [show (o * m) * a * (o * m)⁻¹ = o * (m * a * m⁻¹) * o⁻¹ by group]
      exact h1
    obtain ⟨a', ha'K, ha'eq⟩ : ∃ a' ∈ K₀, a' = (o * m) * a * (o * m)⁻¹ := ⟨_, hg, rfl⟩
    have hmam : m * a * m⁻¹ = o⁻¹ * a' * o := by
      rw [ha'eq]
      group
    have h4 : a'⁻¹ * o⁻¹ * a' ∈ O := by
      have := (mem_normalizer_iff.mp (hMO (hK₀M (K₀.inv_mem ha'K))) o⁻¹).mp (O.inv_mem hoO)
      simpa using this
    have h5 : o⁻¹ * a' * o = a' * (a'⁻¹ * o⁻¹ * a') * o := by group
    rw [hmam, h5]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (mem_sup_left ha'K) (mem_sup_right h4))
      (mem_sup_right hoO)
  have hmap : ∀ m ∈ M, ∀ y ∈ K₀ ⊔ GLBPrimeCore 3 M, m * y * m⁻¹ ∈ K₀ ⊔ GLBPrimeCore 3 M := by
    intro m hm y hy
    have hle : (K₀ ⊔ GLBPrimeCore 3 M).map (MulAut.conj m).toMonoidHom ≤
        K₀ ⊔ GLBPrimeCore 3 M := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨k, hk, rfl⟩
        exact hstar m hm k hk
      · rintro _ ⟨o', ho', rfl⟩
        exact mem_sup_right ((mem_normalizer_iff.mp (hMO hm) o').mp ho')
    exact hle ⟨y, hy, rfl⟩
  intro m hm
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hmap m hm y hy, fun hy => ?_⟩
  have h1 := hmap m⁻¹ (M.inv_mem hm) _ hy
  have e : m⁻¹ * (m * y * m⁻¹) * m⁻¹⁻¹ = y := by group
  rwa [e] at h1

end CFSG.LocalAnalysis.RankThreeTheoremC
