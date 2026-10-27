module

public import CFSG.ClassicalInvolution.AschTight.S1916Ctx
public import CFSG.ClassicalInvolution.AschTight.S1916WEta

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {Y' Q : Subgroup G}

theorem twinSet_omegaPrime' (ht : S19R.TightStd p f K z) (hY : YPrimeData K z Y' Q) :
    twinSet (omegaPrime K Y') Y' = {Y', K} := by
  have hzK := isUniqueInvolution_of_tight ht.toTightBranch
  have hzY := isUniqueInvolution_of_isSylow2In hY.sylow hY.inv hY.le
  have h : twinSet (omegaPrime K Y') Y' = twinSet (omegaPrime K Y') K := by
    ext J
    constructor
    · rintro ⟨hJ, z', hz'Y, hz'J⟩
      exact ⟨hJ, z, hzK, (hz'Y.eq hzY) ▸ hz'J⟩
    · rintro ⟨hJ, z', hz'K, hz'J⟩
      exact ⟨hJ, z, hzY, (hz'K.eq hzK) ▸ hz'J⟩
  rw [h, twinSet_omegaPrime ht hY, Set.pair_comm]

theorem Ctx12.inA_L [IsSimpleGroup G] (c : Ctx12 p f K z S W L t)
    (hY : YPrimeData K z Y' ((S : Subgroup G) ⊓ sec19Y K z)) :
    InA (omegaPrime K Y') Y' L := by
  have hd := c.hd
  have ht := hd.tight
  have hΩ := hypOmegaMod_of_tightD ht
  have hzY := isUniqueInvolution_of_isSylow2In hY.sylow hY.inv hY.le
  have hY'K := not_mem_conjClass_of_centralizes ht hzY hY.cent
  have hLY' : L ≠ Y' := fun h => hY'K (h ▸ c.data.memL)
  refine ⟨⟨Or.inl c.data.memL, hLY', L ⊓ W, USet_mono Set.subset_union_left c.data.memV,
    inf_le_left, fun v hv => hY.normal (hd.hSz (hd.hWS hv.2))⟩, ?_, z, t, hzY, c.data.invL, ?_⟩
  · rintro ⟨-, -, R', hR', hR'L, hR'N⟩
    obtain ⟨M, hM, hR'M⟩ := exists_isSylow2In_of_mem_RSet hR'
    have h1 := natCard_eq_of_isSylow2In_omegaPrime hY hM hR'M
    have h3 : R' ≤ L ⊓ Subgroup.centralizer ({z} : Set G) :=
      le_inf hR'L (hR'N.trans (normalizer_le_centralizer_of_isUniqueInvolution hzY))
    have h4 := c.isSylow2In_V.natCard_le hR'M.2.1 h3
    have h5 := c.card_R
    rw [c.card] at h1
    have hpos : 0 < Nat.card ↥(L ⊓ W) := Nat.card_pos
    omega
  · rintro ⟨g, -, hg⟩
    apply hY'K
    have e : Y' = conjSub g⁻¹ L := by rw [← hg, conjSub_inv_conjSub]
    rw [e]
    exact hΩ.conjInvariant g⁻¹ L c.data.memL

theorem Ctx12.conj_eq_of_le_centralizer (c : Ctx12 p f K z S W L t)
    (hA : ∀ x ∈ (S : Subgroup G), (∀ q ∈ (S : Subgroup G) ⊓ sec19Y K z, x * q = q * x) →
      x ∈ (S : Subgroup G) ⊓ K)
    {g : G} (hg : conjSub g ((S : Subgroup G) ⊓ sec19Y K z) ≤
      Subgroup.centralizer ({z} : Set G)) : g⁻¹ * z * g = z := by
  have hd := c.hd
  have hzK := isUniqueInvolution_of_tight hd.tight.toTightBranch
  set Q := (S : Subgroup G) ⊓ sec19Y K z with hQdef
  have hzQ := sd_isUniqueInvolution_Q hd c.quat
  set u := g⁻¹ * z * g with hu
  have hu2 : u * u = 1 := by
    calc u * u = g⁻¹ * (z * z) * g := by rw [hu]; group
      _ = 1 := by rw [hzK.sq]; group
  have hu1 : u ≠ 1 := by
    intro h
    apply hzK.ne_one
    calc z = g * u * g⁻¹ := by rw [hu]; group
      _ = 1 := by rw [h]; group
  have huQ : ∀ q ∈ Q, q * u = u * q := by
    intro q hq
    have h1 : g * q * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := hg (conj_mem_conjSub hq)
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    calc q * u = g⁻¹ * ((g * q * g⁻¹) * z) * g := by rw [hu]; group
      _ = g⁻¹ * (z * (g * q * g⁻¹)) * g := by rw [h1]
      _ = u * q := by rw [hu]; group
  have huN : u ∈ Subgroup.normalizer (Q : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr huQ)
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (Q : Set G) := fun s hs =>
    mem_normalizer_inf_of_mem hs (sd_centralizer_le_normalizer_Y hd (hd.hSz hs))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hdN, hdS⟩ := exists_conj_le_of_sylow_le S hSN (Subgroup.zpowers_le.mpr huN)
    (isPGroup_zpowers_of_mul_self_eq_one hu2 hu1)
  have hduS : d * u * d⁻¹ ∈ (S : Subgroup G) := hdS (conj_mem_conjSub (Subgroup.mem_zpowers u))
  have hduQ : ∀ q ∈ Q, d * u * d⁻¹ * q = q * (d * u * d⁻¹) := by
    intro q hq
    have hq' : d⁻¹ * q * d ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (Q : Set G)).inv_mem hdN) q).mp hq
      simpa using this
    have h1 := huQ _ hq'
    calc d * u * d⁻¹ * q = d * (u * (d⁻¹ * q * d)) * d⁻¹ := by group
      _ = d * ((d⁻¹ * q * d) * u) * d⁻¹ := by rw [h1]
      _ = q * (d * u * d⁻¹) := by group
  have hR := hA _ hduS hduQ
  have hdz : d * z * d⁻¹ = z := hzQ.conj_eq (mem_normalizer_iff_conjSub_eq.mp hdN)
  have h2 : d * u * d⁻¹ = z := by
    refine ((sd_isUniqueInvolution_R hd).unique _ hR ?_).resolve_left ?_
    · calc d * u * d⁻¹ * (d * u * d⁻¹) = d * (u * u) * d⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    · intro h
      apply hu1
      calc u = d⁻¹ * (d * u * d⁻¹) * d := by group
        _ = 1 := by rw [h]; group
  calc u = d⁻¹ * (d * u * d⁻¹) * d := by group
    _ = d⁻¹ * (d * z * d⁻¹) * d := by rw [h2, hdz]
    _ = z := by group

theorem Ctx12.inA_J [IsSimpleGroup G] (c : Ctx12 p f K z S W L t)
    (hY : YPrimeData K z Y' ((S : Subgroup G) ⊓ sec19Y K z))
    (hA : ∀ x ∈ (S : Subgroup G), (∀ q ∈ (S : Subgroup G) ⊓ sec19Y K z, x * q = q * x) →
      x ∈ (S : Subgroup G) ⊓ K)
    {h : G} (hzh : h * z * h⁻¹ = t) {U : Subgroup G} (hU : U ∈ USet (omegaPrime K Y'))
    (hUJ : U ≤ conjSub h Y') (hUS : U ≤ (S : Subgroup G)) :
    InA (omegaPrime K Y') K (conjSub h Y') := by
  have hd := c.hd
  have ht := hd.tight
  have hΩ := hypOmegaMod_of_tightD ht
  have hzK := isUniqueInvolution_of_tight ht.toTightBranch
  have hzY := isUniqueInvolution_of_isSylow2In hY.sylow hY.inv hY.le
  have hY'K := not_mem_conjClass_of_centralizes ht hzY hY.cent
  have hJt : IsUniqueInvolution (conjSub h Y') t := hzh ▸ hzY.conj h
  have hJ : conjSub h Y' ∈ omegaPrime K Y' := Or.inr ⟨h, rfl⟩
  have hnot : ∀ g : G, conjSub g K ≠ conjSub h Y' := by
    intro g hg
    apply hY'K
    have e : Y' = conjSub h⁻¹ (conjSub g K) := by rw [hg, conjSub_inv_conjSub]
    rw [e]
    exact hΩ.conjInvariant h⁻¹ _ (hΩ.conjInvariant g K (CoreAssembly.mem_conjClass_self K))
  have hJK : conjSub h Y' ≠ K := fun e => hnot 1 (by rw [conjSub_one, e])
  refine ⟨⟨hJ, hJK, U, hU, hUJ, ?_⟩, ?_, z, t, hzK, hJt, ?_⟩
  · intro u hu
    rw [sd_normalizer_eq hd]
    exact hd.hSz (hUS hu)
  · rintro ⟨-, -, R', hR', hR'J, hR'N⟩
    obtain ⟨M, hM, hR'M⟩ := exists_isSylow2In_of_mem_RSet hR'
    have h1 := natCard_eq_of_isSylow2In_omegaPrime hY hM hR'M
    have hJQ := hY.sylow.conj h
    have hR'syl : IsSylow2In R' (conjSub h Y') :=
      hJQ.of_natCard_le hR'M.2.1 hR'J (by rw [natCard_conjSub, h1])
    have hY'syl := hR'syl.conj h⁻¹
    rw [conjSub_inv_conjSub] at hY'syl
    obtain ⟨y, hy, hyQ⟩ := IsSylow2In.exists_conj hY.sylow hY'syl
    have hR'eq : R' = conjSub (h * y) ((S : Subgroup G) ⊓ sec19Y K z) := by
      rw [conjSub_mul, hyQ, conjSub_conjSub_inv]
    have hle : conjSub (h * y) ((S : Subgroup G) ⊓ sec19Y K z) ≤
        Subgroup.centralizer ({z} : Set G) := by
      rw [← hR'eq, ← sd_normalizer_eq hd]
      exact hR'N
    have h2 := c.conj_eq_of_le_centralizer hA hle
    have hyz : y * z * y⁻¹ = z := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hY.le hy)
      calc y * z * y⁻¹ = z * y * y⁻¹ := by rw [this]
        _ = z := by group
    apply c.data.ne
    calc t = h * z * h⁻¹ := hzh.symm
      _ = h * (y * z * y⁻¹) * h⁻¹ := by rw [hyz]
      _ = (h * y) * z * (h * y)⁻¹ := by group
      _ = (h * y) * ((h * y)⁻¹ * z * (h * y)) * (h * y)⁻¹ := by rw [h2]
      _ = z := by group
  · rintro ⟨g, -, hg⟩
    exact hnot g hg

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
