module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44SimpleEleven
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44SimpleShape

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.S44

open Subgroup MulAction

section Glue

variable {V : Type} [CommGroup V]

theorem simple_eq_one_of_fixes {S : Set V} (hS : Subgroup.closure S = ⊤) {k : MulAut V}
    (hk : ∀ v ∈ S, k v = v) : k = 1 := by
  have h : Subgroup.closure S ≤ MonoidHom.eqLocus (k : V →* V) (MonoidHom.id V) :=
    (Subgroup.closure_le _).mpr fun v hv => hk v hv
  rw [hS] at h
  ext v
  exact h (Subgroup.mem_top v)

theorem simple_one_notMem_orbit {X : Subgroup (MulAut V)} {t : V} (ht : t ≠ 1) :
    (1 : V) ∉ orbit X t := by
  rintro ⟨g, hg⟩
  exact ht ((g : MulAut V).map_eq_one_iff.mp hg)

theorem simple_smul_mem_orbit {X : Subgroup (MulAut V)} {t : V} {m : MulAut V} (hm : m ∈ X)
    {b : V} (hb : b ∈ orbit X t) : m b ∈ orbit X t := by
  obtain ⟨g, rfl⟩ := hb
  exact ⟨⟨m, hm⟩ * g, rfl⟩

end Glue

theorem simpleOfShape (hIdx : IdxDvd11Stmt) : SimpleOfShapeStmt := by
  intro V _ _ hV hsq X M t O hMX hO hM _ hν hX hΩ
  obtain ⟨ν, hνX, hνt, hνO⟩ := hν
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have : Finite M := Nat.finite_of_card_ne_zero (by rw [hM]; norm_num)
  have hnt : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by rw [hX]; norm_num)
  refine @IsSimpleGroup.mk X _ hnt ?_
  intro K hKn
  by_cases hbot : K = ⊥
  · exact Or.inl hbot
  refine Or.inr ?_
  have htΩ : t ∈ orbit X t := mem_orbit_self t
  have h1Ω : (1 : V) ∉ orbit X t := simple_one_notMem_orbit hO.ne_one
  have hMΩ : ∀ m ∈ M, ∀ b ∈ orbit X t, m b ∈ orbit X t := fun m hm b hb =>
    simple_smul_mem_orbit (hMX hm) hb
  have hO0 : O 0 ⊆ orbit X t := simple_zero_subset hO hΩ htΩ h1Ω hMΩ
  have hBΩ : orbit K t ⊆ orbit X t := by
    rintro _ ⟨k, rfl⟩
    exact ⟨k, rfl⟩
  have hBinv : ∀ m ∈ M, ∀ b ∈ orbit K t, m b ∈ orbit K t := fun m hm b hb =>
    simple_smul_mem_orbit_normal K (g := ⟨m, hMX hm⟩) (hO.fix m hm) hb
  have hν1 : (⟨ν, hνX⟩ : X) • t = t := hνt
  have hν2 : (⟨ν, hνX⟩ : X)⁻¹ • t = t := inv_smul_eq_iff.mpr hνt.symm
  have h01 : O 0 ⊆ orbit K t ↔ O 1 ⊆ orbit K t := by
    constructor
    · intro h u hu
      rw [← hνO] at hu
      obtain ⟨w, hw, rfl⟩ := hu
      exact simple_smul_mem_orbit_normal K hν1 (h hw)
    · intro h w hw
      have hνw : ν w ∈ O 1 := by
        rw [← hνO]
        exact ⟨w, hw, rfl⟩
      have h3 := simple_smul_mem_orbit_normal K hν2 (h hνw)
      have e : (⟨ν, hνX⟩ : X)⁻¹ • ((⟨ν, hνX⟩ : X) • w) = w := inv_smul_smul _ _
      exact e ▸ h3
  have hdvd : (orbit K t).ncard ∣ 276 := by
    have h := simple_ncard_orbit_dvd (G := X) K t
    rwa [hΩ] at h
  rcases simple_ncard_block hO hΩ htΩ h1Ω hMΩ hBΩ (mem_orbit_self t) hBinv h01 hdvd with
    h1 | h276
  · exfalso
    apply hbot
    obtain ⟨c, hc⟩ := Set.ncard_eq_one.mp h1
    have hKfix : ∀ k ∈ K, k • t = t := by
      intro k hk
      have h2 : k • t ∈ orbit K t := ⟨⟨k, hk⟩, rfl⟩
      have h3 : t ∈ orbit K t := mem_orbit_self t
      rw [hc] at h2 h3
      exact h2.trans h3.symm
    rw [Subgroup.eq_bot_iff_forall]
    intro k hk
    have hk1 : (k : MulAut V) = 1 := by
      refine simple_eq_one_of_fixes hO.gen fun v hv => ?_
      rcases hv with rfl | hv
      · exact simple_smul_eq_of_fixes K hKfix htΩ hk
      · exact simple_smul_eq_of_fixes K hKfix (hO0 hv) hk
    exact Subtype.ext hk1
  · have hKdvd : 276 ∣ Nat.card K := by
      have h := simple_ncard_orbit_dvd_card (G := K) t
      rwa [h276] at h
    have h23 : 23 ∣ Nat.card K := dvd_trans (by norm_num) hKdvd
    have hidx : K.index ∣ 11 := hIdx hV hsq X hX K hKn h23
    rcases (Nat.dvd_prime (by norm_num)).mp hidx with h1 | h11
    · exact Subgroup.index_eq_one.mp h1
    · exfalso
      let ι : M →* X := Subgroup.inclusion hMX
      have hWn : (K.comap ι).Normal := hKn.comap ι
      have hWdvd : (K.comap ι).index ∣ 11 := by
        rw [Subgroup.index_comap]
        have h := Subgroup.relIndex_dvd_index_of_normal K ι.range
        rwa [h11] at h
      have hKcard : Nat.card K * 11 = 244823040 := by
        have h := Subgroup.card_mul_index K
        rwa [h11, hX] at h
      have hW1 : (K.comap ι).index ≠ 1 := by
        intro h
        have htop : K.comap ι = ⊤ := Subgroup.index_eq_one.mp h
        have hmem : ∀ m : M, ι m ∈ K := fun m => by
          have hm : m ∈ K.comap ι := by rw [htop]; exact Subgroup.mem_top m
          exact hm
        have hd : Nat.card M ∣ Nat.card K :=
          Subgroup.card_dvd_of_injective (ι.codRestrict K hmem) fun a b hab =>
            Subgroup.inclusion_injective hMX (congrArg Subtype.val hab)
        rw [hM] at hd
        omega
      have hW11 : (K.comap ι).index = 11 := by
        rcases (Nat.dvd_prime (by norm_num)).mp hWdvd with h | h
        · exact absurd h hW1
        · exact h
      obtain ⟨x0, hx0⟩ := hO.isOrbit 0
      obtain ⟨x2, hx2⟩ := hO.isOrbit 2
      refine simple_no_index_eleven (M := M) (V := V)
        (fun m u u' => map_mul (m : MulAut V) u u') (K.comap ι) hW11 hM (x := x0) (y := x2) ?_ ?_ ?_
      · rw [← hx0]
        exact hO.ncard 0
      · rw [← hx2]
        exact hO.ncard 2
      · rw [← hx0, ← hx2]
        exact hO.prod

end CFSG.EvenSporadicStandard.TwoFi22.DS81.S44
