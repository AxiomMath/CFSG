module

public import CFSG.ClassicalInvolution.Asc77.AscS24BFrame

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace S24B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem exists_rep_of_le {W : Subgroup G} (c : Thompson.Ctx p f Ω W) {S₀ : Sylow 2 G}
    (hWS₀ : W ≤ (S₀ : Subgroup G)) {J T : Subgroup G} (hJ : J ∈ Ω) (hT : T ∈ RSet Ω)
    (hTJ : T ≤ J) (hTS : T ≤ (S₀ : Subgroup G)) :
    ∃ ρ : Thompson.Rep Ω W, ρ.K = J ∧ ρ.R = T := by
  have hTD : T ∈ DSet Ω W := Thompson.mem_DSet_of_le_sylow c.hp c.hq c.hΩ c.hW hWS₀ hT hTS
  have hTsyl : IsSylow2In T J := T7C.isSylow2In_of_mem_RSet_of_le c.hp c.hΩ hJ hT hTJ
  have hcard := Thompson.D_card c.hp c.hq c.hΩ c.hW hTD
  have hpos : 0 < Nat.card ↥T := Nat.card_pos
  have hnot : ¬ T ≤ W := by
    intro hle
    have : T ⊓ W = T := inf_eq_left.mpr hle
    rw [this] at hcard
    omega
  obtain ⟨r, hrT, hrW⟩ := Set.not_subset.mp hnot
  exact ⟨⟨J, T, r, hJ, hTD, hTsyl, hrT, hrW⟩, rfl, rfl⟩

namespace Ctx8

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Ctx8 p f Ω K K' W S R R' z u)

include C in
theorem card_K_inf_W : Nat.card ↥(K ⊓ W) = 4 := by
  have h := (Thompson.inf_W_of_mem_D C.D.c.hp C.D.c.hq C.D.c.hΩ C.D.c.hW C.D.F.ρ.hR
    C.D.F.ρ.hK C.D.F.ρ.hRK).1
  rw [C.hK] at h
  rw [← h, ← C.D.h₁, Nat.card_zpowers, C.orderOf_x₁]

theorem card_J_inf_W : Nat.card ↥(C.D.F.ρ₃.K ⊓ W) = 4 := by
  have h := (Thompson.inf_W_of_mem_D C.D.c.hp C.D.c.hq C.D.c.hΩ C.D.c.hW C.D.F.ρ₃.hR
    C.D.F.ρ₃.hK C.D.F.ρ₃.hRK).1
  rw [← h, ← C.D.h₃, Nat.card_zpowers, C.orderOf_x₃]

include C in
theorem not_alt_two {S₀ : Sylow 2 G} (hWS₀ : W ≤ (S₀ : Subgroup G))
    (h2 : ∀ L ∈ Ω, 2 < Nat.card ↥(L ⊓ (S₀ : Subgroup G)) → L ⊓ (S₀ : Subgroup G) ∈ RSet Ω) :
    False := by
  have hst := C.hs.stand
  set J := C.D.F.ρ₃.K with hJdef
  have hKS : 2 < Nat.card ↥(K ⊓ (S₀ : Subgroup G)) :=
    lt_of_lt_of_le (by rw [C.card_K_inf_W]; norm_num)
      (Subgroup.card_le_of_le (inf_le_inf_left K hWS₀))
  have hJS : 2 < Nat.card ↥(J ⊓ (S₀ : Subgroup G)) :=
    lt_of_lt_of_le (by rw [C.card_J_inf_W]; norm_num)
      (Subgroup.card_le_of_le (inf_le_inf_left J hWS₀))
  have hK1 := h2 K hst.mem hKS
  have hJ1 := h2 J C.D.F.ρ₃.hK hJS
  obtain ⟨ρa, hρaK, hρaR⟩ := exists_rep_of_le C.D.c hWS₀ hst.mem hK1 inf_le_left inf_le_right
  obtain ⟨ρb, hρbK, hρbR⟩ :=
    exists_rep_of_le C.D.c hWS₀ C.D.F.ρ₃.hK hJ1 inf_le_left inf_le_right
  have hne : K ⊓ (S₀ : Subgroup G) ≠ J ⊓ (S₀ : Subgroup G) := by
    intro h
    have hle : K ⊓ (S₀ : Subgroup G) ≤ J := h ▸ inf_le_left
    have h4 : 4 ≤ Nat.card ↥(K ⊓ (S₀ : Subgroup G)) := by
      have := Subgroup.card_le_of_le (inf_le_inf_left K hWS₀)
      rw [C.card_K_inf_W] at this
      exact this
    exact C.D.F.hne₁ (C.hK.trans (hst.hyp.eq_of_le_of_le hst.mem C.D.F.ρ₃.hK
      (S₀.isPGroup'.to_inf_right) h4 inf_le_left hle))
  have hcomm := l6_7_proved p f hst.odd hst.five G Ω hst.hyp S₀ _ hK1 _ hJ1 inf_le_right
    inf_le_right hne
  have hab : ρa.r * ρb.r = ρb.r * ρa.r :=
    hcomm _ (hρaR ▸ ρa.hr) _ (hρbR ▸ ρb.hr)
  have hia : ρa.img = C.D.F.ρ.img := C.D.c.img_eq_of_K_eq ρa C.D.F.ρ (hρaK.trans C.hK.symm)
  have hib : ρb.img = C.D.F.ρ₃.img := C.D.c.img_eq_of_K_eq ρb C.D.F.ρ₃ hρbK
  apply C.D.hac
  apply Subtype.ext
  change C.D.F.ρ.img * C.D.F.ρ₃.img = C.D.F.ρ₃.img * C.D.F.ρ.img
  rw [← hia, ← hib]
  unfold Thompson.Rep.img
  rw [← Thompson.piG_mul ρa.r_mem_normalizer ρb.r_mem_normalizer,
    ← Thompson.piG_mul ρb.r_mem_normalizer ρa.r_mem_normalizer, hab]

include C in
theorem le_normalizer_W : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := by
  have hst := C.hs.stand
  obtain ⟨η, hηG, hWη⟩ := id C.hd.hW
  obtain ⟨S₀, hηS₀, hinv⟩ := id hηG
  have hUS₀ : ∀ U ∈ η, U ≤ (S₀ : Subgroup G) := fun U hU => (hηS₀.1 hU).2
  have hWS₀ : W ≤ (S₀ : Subgroup G) := by
    rw [hWη]; exact iSup₂_le fun U hU => hUS₀ U hU
  have hP : PartIHyp p f Ω := ⟨hst.odd, hst.five, hst.hyp, hst.aEmpty⟩
  have htr : ∀ K₁ ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K₁ = J := by
    intro K₁ hK₁ J hJ
    obtain ⟨g₁, rfl⟩ := hst.trans K₁ hK₁
    obtain ⟨g₂, rfl⟩ := hst.trans J hJ
    exact ⟨g₂ * g₁⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  have h612 := AschTight.Sec7.l6_12_mod p f G Ω hP htr S₀
  dsimp only at h612
  rcases h612 with ⟨η₀, -, -, huniq, hwc⟩ | h2
  · have hMS₀ : (⨆ U ∈ {U : Subgroup G | (∃ η ∈ etaG Ω, U ∈ η) ∧ U ≤ (S₀ : Subgroup G)}, U) ≤
        (S₀ : Subgroup G) := iSup₂_le fun U hU => hU.2
    have hηeq : η = η₀ := huniq η hηG fun m hm U hU => hinv m (hMS₀ hm) U hU
    subst hηeq
    intro s hs
    obtain ⟨x, hx⟩ := exists_conjSub_eq_of_sylow S₀ S
    have hU_S : ∀ U ∈ η, U ≤ (S : Subgroup G) := fun U hU =>
      (hWη ▸ le_iSup₂ (f := fun V (_ : V ∈ η) => V) U hU : U ≤ W).trans C.hd.hWS
    have hback : ∀ {A : Subgroup G}, A ≤ (S : Subgroup G) →
        conjSub x⁻¹ A ≤ (S₀ : Subgroup G) := fun {A} hA => by
      rw [conjSub_le_iff, inv_inv, hx]; exact hA
    have h1 : ∀ U ∈ η, conjSub (x⁻¹ * s) U ∈ η := by
      refine hwc (x⁻¹ * s) fun U hU => ?_
      rw [conjSub_mul]
      refine hback ?_
      have h := conjSub_mono (n := s) (hU_S U hU)
      rwa [conjSub_eq_self_of_mem hs] at h
    have h2 : ∀ U ∈ η, conjSub x⁻¹ U ∈ η := hwc x⁻¹ fun U hU => hback (hU_S U hU)
    have e1 : conjSub (x⁻¹ * s) W = W := by
      rw [hWη]; exact AschTight.Sec7.conjSub_iSup_eq_of_forall_mem h1
    have e2 : conjSub x⁻¹ W = W := by
      rw [hWη]; exact AschTight.Sec7.conjSub_iSup_eq_of_forall_mem h2
    have e3 : conjSub x W = W := by
      conv_lhs => rw [← e2]
      exact conjSub_conjSub_inv x W
    refine mem_normalizer_iff_conjSub_eq.mpr ?_
    calc conjSub s W = conjSub (x * (x⁻¹ * s)) W := by group
      _ = W := by rw [conjSub_mul, e1, e3]
  · exact (C.not_alt_two hWS₀ h2).elim

include C in
theorem hRsyl : IsSylow2In R K :=
  T7C.isSylow2In_of_mem_RSet_of_le C.hs.stand.odd C.hs.stand.hyp C.hs.stand.mem C.hd.hR.1
    C.hd.hR.2.1

include C in
theorem z_mem_R : z ∈ R :=
  T7C.mem_of_isSylow2In C.hs.stand.odd C.hs.stand.hyp C.hs.stand.mem C.hRsyl C.hzK

include C in
theorem conjSub_K_mem {y : G} (hy : y ∈ (S : Subgroup G)) :
    conjSub y K = K ∨ conjSub y K = K' := by
  have hst := C.hs.stand
  have hΩ := hst.hyp
  have hT : conjSub y R ∈ RSet Ω := RSet.conj hΩ.conjInvariant C.hd.hR.1 y
  have hTS : conjSub y R ≤ (S : Subgroup G) := by
    have h := conjSub_mono (n := y) C.hd.hR.2.2
    rwa [conjSub_eq_self_of_mem hy] at h
  have hL : conjSub y K ∈ Ω := hΩ.conjInvariant y K hst.mem
  have hTL : conjSub y R ≤ conjSub y K := conjSub_mono C.hd.hR.2.1
  have hT2 : IsPGroup 2 ↥(conjSub y R) := S.isPGroup'.to_le hTS
  have h8 : Nat.card ↥(conjSub y R) = 8 := by
    rw [← C.h8]
    exact Nat.card_congr (Subgroup.equivMapOfInjective R (MulAut.conj y).toMonoidHom
      (MulAut.conj y).injective).symm.toEquiv
  by_cases hTR : conjSub y R = R
  · left
    exact (hΩ.eq_of_le_of_le hst.mem hL hT2 (by omega) ((le_of_eq hTR).trans C.hd.hR.2.1)
      hTL).symm
  · by_cases hLK : conjSub y K = K
    · exact Or.inl hLK
    · right
      have hcomm := l6_7_proved p f hst.odd hst.five G Ω hΩ S R C.hd.hR.1 _ hT C.hd.hR.2.2 hTS
        (Ne.symm hTR)
      have hTc : conjSub y R ≤ Subgroup.centralizer ({z} : Set G) := fun t ht => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm z C.z_mem_R t ht).symm
      have hTN := hΩ.le_normalizer_of_le_centralizer hst.odd hst.five hst.mem hL (Ne.symm hLK)
        C.hzK hTL hT2 (by omega) hTc
      have hnbr : conjSub y K ∈ omegaNbr Ω K := ⟨hL, hLK, _, hT, hTL, hTN⟩
      have hperp : conjSub y K ∈ KPerp Ω K := Set.mem_insert_of_mem _ hnbr
      rw [C.hs.perp] at hperp
      rcases hperp with h | h
      · exact absurd h hLK
      · exact h

include C in
theorem le_centralizer_z : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := C.hzK.conj y
  have h2 : y * z * y⁻¹ = z := by
    rcases C.conjSub_K_mem hy with h | h
    · rw [h] at h1; exact (C.hzK.eq h1).symm
    · rw [h] at h1; exact (C.hzK'.eq h1).symm
  calc y * z = y * z * y⁻¹ * y := by group
    _ = z * y := by rw [h2]

end Ctx8

end S24B

end CFSG.ClassicalInvolution.Asc77
