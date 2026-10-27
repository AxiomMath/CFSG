module

public import CFSG.Open.GLBDefs
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMDataAux2
import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoDataAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G}
  {L : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem exists_lift_of_ppd_of_map {M U Z : Subgroup G} (hUH : U ≤ H) (hUp : IsPGroup p U)
    (hZU : Z ≤ U) (hNHM : GLBPrimeCore p H ≤ H ⊓ M) {T₁ : Sylow p L}
    (hUmap : (U.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (T₁ : Subgroup L).map L.subtype)
    (hZmap : (Z.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      ((T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L)).map L.subtype)
    (hNle : L ⊓ Subgroup.normalizer ((((T₁ : Subgroup L).map L.subtype :
        Subgroup (H ⧸ primeComplementCore (G := H) p))) :
        Set (H ⧸ primeComplementCore (G := H) p)) ≤
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
    {r : ℕ} [Fact r.Prime] {c : L} (hcN : c ∈ Subgroup.normalizer ((T₁ : Subgroup L) : Set L))
    (hcord : orderOf c = r)
    (hcirr : ∀ k : ℕ, ¬ r ∣ k →
      (∃ u ∈ (T₁ : Subgroup L), c ^ k * u * (c ^ k)⁻¹ * u⁻¹ ∉
        (T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L)) ∧
      ∀ V : Subgroup L,
        (T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L) ≤ V →
        V ≤ T₁ → c ^ k ∈ Subgroup.normalizer (V : Set L) →
        V = (T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L) ∨ V = T₁) :
    ∃ t : G, t ∈ H ⊓ M ∧ t ∈ Subgroup.normalizer (U : Set G) ∧
      IsPGroup r (Subgroup.zpowers t) ∧ (∀ u ∈ U, t ^ r * u * (t ^ r)⁻¹ = u) ∧
      (∃ u ∈ U, t * u * t⁻¹ * u⁻¹ ∉ Z) ∧
      ∀ V : Subgroup G, Z ≤ V → V ≤ U → t ∈ Subgroup.normalizer (V : Set G) → V = Z ∨ V = U := by
  have hp : p.Prime := Fact.out
  have hr : r.Prime := Fact.out
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set T : Subgroup (H ⧸ primeComplementCore (G := H) p) := (T₁ : Subgroup L).map L.subtype
    with hTdef
  have hUN : U ⊓ GLBPrimeCore p H = ⊥ := inf_eq_bot_of_isPGroup hp hUp (glbPrimeCore_coprime p H)
  have hinj : ∀ {A B : Subgroup G}, A ≤ U → B ≤ U →
      (A.subgroupOf H).map π ≤ (B.subgroupOf H).map π → A ≤ B :=
    fun hAU hBU hAB => le_of_map_mk_le_of_isPGroup hUH hUp hAU hBU hAB
  have hcY : (c : H ⧸ primeComplementCore (G := H) p) ∈
      L ⊓ Subgroup.normalizer (T : Set (H ⧸ primeComplementCore (G := H) p)) :=
    coe_mem_normalizer_map hcN
  obtain ⟨k, hk, hkc⟩ := hNle hcY
  have hkN : k ∈ (Subgroup.normalizer (((U.subgroupOf H).map π : Subgroup _) :
      Set (H ⧸ primeComplementCore (G := H) p))).comap π := by
    rw [Subgroup.mem_comap, hkc, hUmap]
    exact hcY.2
  obtain ⟨o, ho, t₀, ht₀, hot⟩ := Subgroup.mem_sup_of_normal_left.mp
    (comap_normalizer_map_le_sup hp (primeComplementCore (G := H) p)
      (primeComplementCore_coprime p) hUp.comap_subtype hkN)
  have hoN : ((o : H) : G) ∈ GLBPrimeCore p H :=
    (mem_glbPrimeCore_iff_mk_eq_one o).mpr ((QuotientGroup.eq_one_iff o).mpr ho)
  have ht₀K : (t₀ : G) ∈ H ⊓ M := by
    have : (t₀ : G) = ((o : H) : G)⁻¹ * (k : G) := by rw [← hot]; simp
    rw [this]
    exact (H ⊓ M).mul_mem ((H ⊓ M).inv_mem (hNHM hoN)) (Subgroup.mem_subgroupOf.mp hk)
  have ho1 : π o = 1 := by
    rw [hπ, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff o).mpr ho
  have hπt₀ : π t₀ = c := by rw [← hkc, ← hot, map_mul, ho1, one_mul]
  have ht₀U : (t₀ : G) ∈ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have := (Subgroup.mem_normalizer_iff.mp ht₀ ⟨g, hUH hg⟩).mp
        (Subgroup.mem_subgroupOf.mpr hg)
      simpa using Subgroup.mem_subgroupOf.mp this
    · intro hg
      have hgH : g ∈ H := by
        have e : g = (t₀ : G)⁻¹ * ((t₀ : G) * g * (t₀ : G)⁻¹) * t₀ := by group
        rw [e]
        exact H.mul_mem (H.mul_mem (H.inv_mem t₀.2) (hUH hg)) t₀.2
      have := (Subgroup.mem_normalizer_iff.mp ht₀ ⟨g, hgH⟩).mpr
        (Subgroup.mem_subgroupOf.mpr (by simpa using hg))
      exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨e', m, hm, hom⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos t₀).ne' r hr.one_lt.ne'
  set t : G := (t₀ : G) ^ m with htdef
  have htK : t ∈ H ⊓ M := (H ⊓ M).pow_mem ht₀K m
  have htU : t ∈ Subgroup.normalizer (U : Set G) := Subgroup.pow_mem _ ht₀U m
  have htH : t ∈ H := htK.1
  have hπt : ∀ j : ℕ, π ⟨t ^ j, H.pow_mem htH j⟩ = (c : H ⧸ _) ^ (m * j) := by
    intro j
    have : (⟨t ^ j, H.pow_mem htH j⟩ : H) = t₀ ^ (m * j) := by
      apply Subtype.ext
      simp [htdef, pow_mul]
    rw [this, map_pow, hπt₀]
  have hπt1 : π ⟨t, htH⟩ = (c : H ⧸ _) ^ m := by simpa using hπt 1
  have htr : IsPGroup r (Subgroup.zpowers t) := by
    have h1 : t ^ r ^ e' = 1 := by
      rw [htdef, ← pow_mul, mul_comm, ← hom]
      have : (t₀ : G) ^ orderOf t₀ = 1 := by
        rw [← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
      exact this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hr).mp (orderOf_dvd_of_pow_eq_one h1)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  have hcr : c ^ r = 1 := by rw [← hcord]; exact pow_orderOf_eq_one c
  have htrU : ∀ u ∈ U, t ^ r * u * (t ^ r)⁻¹ = u := by
    intro u hu
    have htrN : t ^ r ∈ GLBPrimeCore p H := by
      have h0 : π ⟨t ^ r, H.pow_mem htH r⟩ = 1 := by
        rw [hπt r, pow_mul', ← Subgroup.coe_pow, hcr, Subgroup.coe_one, one_pow]
      exact (mem_glbPrimeCore_iff_mk_eq_one (p := p) ⟨t ^ r, H.pow_mem htH r⟩).mpr h0
    have h1 : t ^ r * u * (t ^ r)⁻¹ * u⁻¹ ∈ U :=
      U.mul_mem ((Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ htU r) u).mp hu)
        (U.inv_mem hu)
    have h2 : t ^ r * u * (t ^ r)⁻¹ * u⁻¹ ∈ GLBPrimeCore p H := by
      have hn := (le_normalizer_glbPrimeCore p H) (hUH hu)
      have h3 : u * (t ^ r)⁻¹ * u⁻¹ ∈ GLBPrimeCore p H :=
        (Subgroup.mem_normalizer_iff.mp hn _).mp ((GLBPrimeCore p H).inv_mem htrN)
      have e : t ^ r * u * (t ^ r)⁻¹ * u⁻¹ = t ^ r * (u * (t ^ r)⁻¹ * u⁻¹) := by group
      rw [e]
      exact (GLBPrimeCore p H).mul_mem htrN h3
    have h4 : t ^ r * u * (t ^ r)⁻¹ * u⁻¹ = 1 := by
      have hmem : t ^ r * u * (t ^ r)⁻¹ * u⁻¹ ∈ U ⊓ GLBPrimeCore p H := ⟨h1, h2⟩
      rwa [hUN, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.mp h4
  obtain ⟨⟨u₁, hu₁T, hu₁Z⟩, hcV⟩ := hcirr m hm
  have hu₁U : ((u₁ : L) : H ⧸ primeComplementCore (G := H) p) ∈ (U.subgroupOf H).map π := by
    rw [hUmap]
    exact ⟨u₁, hu₁T, rfl⟩
  obtain ⟨⟨u, huH⟩, hu, hπu⟩ := hu₁U
  refine ⟨t, htK, htU, htr, htrU, ⟨u, Subgroup.mem_subgroupOf.mp hu, fun hZc => hu₁Z ?_⟩,
    fun V hZV hVU htV => ?_⟩
  · have hmem : π (⟨t, htH⟩ * ⟨u, huH⟩ * (⟨t, htH⟩ : H)⁻¹ * (⟨u, huH⟩ : H)⁻¹) ∈
        (Z.subgroupOf H).map π :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (by simpa using hZc))
    rw [hZmap, map_mul, map_mul, map_mul, map_inv, map_inv, hπt1, hπu] at hmem
    have hmem' : L.subtype (c ^ m * u₁ * (c ^ m)⁻¹ * u₁⁻¹) ∈
        ((T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L)).map L.subtype := by
      simpa using hmem
    exact (Subgroup.mem_map_iff_mem L.subtype_injective).mp hmem'
  · set V' := (V.subgroupOf H).map π with hV'
    have hZV' : ((T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L)).map
        L.subtype ≤ V' := hZmap ▸ Subgroup.map_mono (Subgroup.subgroupOf_mono H hZV)
    have hVT : V' ≤ T := hUmap ▸ Subgroup.map_mono (Subgroup.subgroupOf_mono H hVU)
    have hcV' : (c : H ⧸ primeComplementCore (G := H) p) ^ m ∈
        Subgroup.normalizer (V' : Set (H ⧸ primeComplementCore (G := H) p)) := by
      rw [← hπt1]
      exact map_mk_le_normalizer_map_mk (A := Subgroup.zpowers t) (Y := V)
        ((Subgroup.zpowers_le).mpr htV)
        ⟨⟨t, htH⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers t), rfl⟩
    have hVL : V' ≤ L := hVT.trans (Subgroup.map_subtype_le _)
    have hWmap : (V'.subgroupOf L).map L.subtype = V' := Subgroup.map_subgroupOf_eq_of_le hVL
    have hZW : (T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L) ≤
        V'.subgroupOf L := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hZV' ⟨x, hx, rfl⟩)
    have hWT : V'.subgroupOf L ≤ T₁ := by
      intro x hx
      have h1 : (x : H ⧸ primeComplementCore (G := H) p) ∈ T :=
        hVT (Subgroup.mem_subgroupOf.mp hx)
      exact (Subgroup.mem_map_iff_mem L.subtype_injective).mp h1
    have hcW : c ^ m ∈ Subgroup.normalizer ((V'.subgroupOf L : Subgroup L) : Set L) :=
      Subgroup.le_normalizer_comap L.subtype
        (show L.subtype (c ^ m) ∈ _ by rw [map_pow]; exact hcV')
    rcases hcV _ hZW hWT hcW with hWZ | hWT'
    · left
      have h1 : V' = (Z.subgroupOf H).map π := by rw [← hWmap, hWZ, hZmap]
      exact le_antisymm (hinj hVU hZU h1.le) hZV
    · right
      have h1 : V' = (U.subgroupOf H).map π := by rw [← hWmap, hWT', hUmap]
      exact le_antisymm hVU (hinj le_rfl hVU h1.ge)

end CFSG.AGLEmbedding
