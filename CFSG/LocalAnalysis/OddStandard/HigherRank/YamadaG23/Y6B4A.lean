module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4Def
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54One
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6E26B

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y6b_mem_sup_invol {K : Subgroup G} {u : G} (hu : u * u = 1)
    (hK : ∀ k ∈ K, k * u = u * k) {x : G} :
    x ∈ K ⊔ zpowers u ↔ ∃ k ∈ K, x = k ∨ x = k * u := by
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  let S : Subgroup G :=
    { carrier := {x | ∃ k ∈ K, x = k ∨ x = k * u}
      mul_mem' := by
        rintro x y ⟨kx, hkx, hx | hx⟩ ⟨ky, hky, hy | hy⟩
        · exact ⟨kx * ky, K.mul_mem hkx hky, Or.inl (by rw [hx, hy])⟩
        · exact ⟨kx * ky, K.mul_mem hkx hky, Or.inr (by rw [hx, hy, ← mul_assoc])⟩
        · exact ⟨kx * ky, K.mul_mem hkx hky,
            Or.inr (by rw [hx, hy, mul_assoc, ← hK ky hky, ← mul_assoc])⟩
        · exact ⟨kx * ky, K.mul_mem hkx hky, Or.inl (by
            rw [hx, hy]
            calc (kx * u) * (ky * u) = kx * ky * (u * u) :=
                  Commute.mul_mul_mul_comm (show Commute u ky from (hK ky hky).symm) kx u
              _ = kx * ky := by rw [hu, mul_one])⟩
      one_mem' := ⟨1, K.one_mem, Or.inl rfl⟩
      inv_mem' := by
        rintro x ⟨k, hk, hx | hx⟩
        · exact ⟨k⁻¹, K.inv_mem hk, Or.inl (by rw [hx])⟩
        · exact ⟨k⁻¹, K.inv_mem hk,
            Or.inr (by rw [hx, mul_inv_rev, hu_inv, hK k⁻¹ (K.inv_mem hk)])⟩ }
  constructor
  · intro hx
    have hS : K ⊔ zpowers u ≤ S :=
      sup_le (fun k hk => ⟨k, hk, Or.inl rfl⟩)
        (Subgroup.zpowers_le.mpr (show u ∈ S from ⟨1, K.one_mem, Or.inr (one_mul u).symm⟩))
    exact hS hx
  · rintro ⟨k, hk, hx | hx⟩
    · rw [hx]; exact Subgroup.mem_sup_left hk
    · rw [hx]
      exact Subgroup.mul_mem_sup hk (Subgroup.mem_zpowers u)

theorem y6b_g_sq (c : Ctx5 G L) (hRT : c.s.R ≠ c.s.T) : c.g * c.g = 1 := by
  have h := (c.g_spec hRT).2.2.2.1
  simpa [pow_two] using h

theorem y6b_t_sq (c : Ctx5 G L) : c.s.t * c.s.t = 1 := by
  have h := pow_orderOf_eq_one c.s.t
  rw [c.s.t_order] at h
  simpa [pow_two] using h

theorem y6b_g_mem_T (c : Ctx5 G L) (hRT : c.s.R ≠ c.s.T) : c.g ∈ c.s.T :=
  (c.g_spec hRT).1

theorem y6b_g_comm_t (c : Ctx5 G L) (hRT : c.s.R ≠ c.s.T) : c.g * c.s.t = c.s.t * c.g := by
  have hgH : c.g ∈ c.s.H := c.s.sylow_T.1 (y6b_g_mem_T c hRT)
  exact ((Subgroup.mem_centralizer_iff.mp hgH) c.s.t (Set.mem_singleton _)).symm

theorem y6b_g_comm_F (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    ∀ f ∈ c.s.fr.F, c.g * f = f * c.g := by
  intro f hf
  have h := y5_g_cent_F hH (by simpa [pow_two] using y6b_g_sq c hRT)
    (c.g_spec hRT).2.2.1 f hf
  rwa [mul_inv_eq_iff_eq_mul] at h

theorem y6b_g_not_mem_M (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    c.g ∉ L ⊔ centIn c.s.H L :=
  s3_not_mem_M c.s hH.hS (y6b_g_mem_T c hRT) (c.g_spec hRT).2.1

theorem y6b_g_not_mem_F (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    c.g ∉ c.s.fr.F := by
  intro hgF
  exact y6b_g_not_mem_M c hH hRT (Subgroup.mem_sup_left (y54_F_le_L c.s hgF))

theorem y6b_F_le_E16 (c : Ctx5 G L) : c.s.fr.F ≤ y6bE16 c := le_sup_left

theorem y6b_g_mem_E16 (c : Ctx5 G L) : c.g ∈ y6bE16 c :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers c.g)

theorem y6b_E16_le_E (c : Ctx5 G L) : y6bE16 c ≤ y6bE c := le_sup_left

theorem y6b_t_mem_E (c : Ctx5 G L) : c.s.t ∈ y6bE c :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t)

theorem y6b_F_le_E (c : Ctx5 G L) : c.s.fr.F ≤ y6bE c := (y6b_F_le_E16 c).trans (y6b_E16_le_E c)

theorem y6b_mem_E16 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) {x : G} :
    x ∈ y6bE16 c ↔ ∃ f ∈ c.s.fr.F, x = f ∨ x = f * c.g := by
  rw [y6bE16]
  exact y6b_mem_sup_invol (y6b_g_sq c hRT)
    (fun f hf => (y6b_g_comm_F c hH hRT f hf).symm)

private lemma y6b_t_comm_E16 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    ∀ k ∈ y6bE16 c, k * c.s.t = c.s.t * k := by
  intro k hk
  obtain ⟨f, hf, h | h⟩ := (y6b_mem_E16 c hH hRT).mp hk
  · rw [h]; exact y54_t_comm_F c.s f hf
  · rw [h, mul_assoc, y6b_g_comm_t c hRT, ← mul_assoc, y54_t_comm_F c.s f hf, mul_assoc]

theorem y6b_mem_E (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) {x : G} :
    x ∈ y6bE c ↔ ∃ f ∈ c.s.fr.F, x = f ∨ x = f * c.g ∨ x = f * c.s.t ∨
      x = f * (c.g * c.s.t) := by
  rw [y6bE, y6b_mem_sup_invol (y6b_t_sq c) (y6b_t_comm_E16 c hH hRT)]
  constructor
  · rintro ⟨k, hk, h⟩
    obtain ⟨f, hf, h'⟩ := (y6b_mem_E16 c hH hRT).mp hk
    rcases h with h | h
    · rcases h' with h' | h'
      · exact ⟨f, hf, Or.inl (h.trans h')⟩
      · exact ⟨f, hf, Or.inr (Or.inl (h.trans h'))⟩
    · rcases h' with h' | h'
      · exact ⟨f, hf, Or.inr (Or.inr (Or.inl (h.trans (by rw [h']))))⟩
      · exact ⟨f, hf, Or.inr (Or.inr (Or.inr (h.trans (by rw [h', mul_assoc]))))⟩
  · rintro ⟨f, hf, h⟩
    rcases h with h | h | h | h
    · exact ⟨f, (y6b_mem_E16 c hH hRT).mpr ⟨f, hf, Or.inl rfl⟩, Or.inl h⟩
    · exact ⟨f * c.g, (y6b_mem_E16 c hH hRT).mpr ⟨f, hf, Or.inr rfl⟩, Or.inl h⟩
    · exact ⟨f, (y6b_mem_E16 c hH hRT).mpr ⟨f, hf, Or.inl rfl⟩, Or.inr h⟩
    · exact ⟨f * c.g, (y6b_mem_E16 c hH hRT).mpr ⟨f, hf, Or.inr rfl⟩,
        Or.inr (h.trans (mul_assoc f c.g c.s.t).symm)⟩

theorem y6b_t_not_mem_E16 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    c.s.t ∉ y6bE16 c := by
  intro ht
  obtain ⟨f, hf, h | h⟩ := (y6b_mem_E16 c hH hRT).mp ht
  · exact s3_t_not_mem_L c.s hH.h31 (y54_F_le_L c.s (by rwa [← h] at hf))
  · apply y6b_g_not_mem_M c hH hRT
    have hg : c.g = f⁻¹ * c.s.t := by rw [h]; group
    rw [hg]
    exact Subgroup.mul_mem_sup (y54_F_le_L c.s (c.s.fr.F.inv_mem hf))
      (by rw [f3_centIn_H_L hH]; exact Subgroup.mem_zpowers c.s.t)

private lemma y6bE_mem_form (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T)
    {x : G} (hx : x ∈ y6bE c) :
    ∃ f ∈ c.s.fr.F, ∃ a ∈ ({1, c.g, c.s.t, c.g * c.s.t} : Set G), x = f * a := by
  obtain ⟨f, hf, h⟩ := (y6b_mem_E c hH hRT).mp hx
  rcases h with h | h | h | h
  · exact ⟨f, hf, 1, by simp, by rw [h, mul_one]⟩
  · exact ⟨f, hf, c.g, by simp, h⟩
  · exact ⟨f, hf, c.s.t, by simp, h⟩
  · exact ⟨f, hf, c.g * c.s.t, by simp, h⟩

private lemma y6b_comm_F_unit (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T)
    {f : G} (hf : f ∈ c.s.fr.F) :
    ∀ a ∈ ({1, c.g, c.s.t, c.g * c.s.t} : Set G), Commute f a := by
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact Commute.one_right f
  · exact (y6b_g_comm_F c hH hRT f hf).symm
  · exact y54_t_comm_F c.s f hf
  · exact (show Commute f c.g from (y6b_g_comm_F c hH hRT f hf).symm).mul_right
      (y54_t_comm_F c.s f hf)

private lemma y6b_unit_comm (c : Ctx5 G L) (hRT : c.s.R ≠ c.s.T) :
    ∀ a ∈ ({1, c.g, c.s.t, c.g * c.s.t} : Set G),
    ∀ b ∈ ({1, c.g, c.s.t, c.g * c.s.t} : Set G), Commute a b := by
  have hgt : Commute c.g c.s.t := y6b_g_comm_t c hRT
  have hggt : Commute c.g (c.g * c.s.t) := (Commute.refl c.g).mul_right hgt
  have htgt : Commute c.s.t (c.g * c.s.t) := hgt.symm |>.mul_right (Commute.refl c.s.t)
  intro a ha b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    first
      | exact Commute.one_left _
      | exact Commute.one_right _
      | exact Commute.refl _
      | exact hgt
      | exact hgt.symm
      | exact hggt
      | exact hggt.symm
      | exact htgt
      | exact htgt.symm

private lemma y6b_unit_sq (c : Ctx5 G L) (hRT : c.s.R ≠ c.s.T) :
    ∀ a ∈ ({1, c.g, c.s.t, c.g * c.s.t} : Set G), a ^ 2 = 1 := by
  have hgt : Commute c.g c.s.t := y6b_g_comm_t c hRT
  have hg2 : c.g ^ 2 = 1 := by simpa [pow_two] using y6b_g_sq c hRT
  have ht2 : c.s.t ^ 2 = 1 := by simpa [pow_two] using y6b_t_sq c
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · simp
  · exact hg2
  · exact ht2
  · rw [hgt.mul_pow 2, hg2, ht2, mul_one]

theorem y6b_E_comm (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) {x y : G}
    (hx : x ∈ y6bE c) (hy : y ∈ y6bE c) : x * y = y * x := by
  obtain ⟨f, hf, a, ha, rfl⟩ := y6bE_mem_form c hH hRT hx
  obtain ⟨f', hf', b, hb, rfl⟩ := y6bE_mem_form c hH hRT hy
  have hff' : Commute f f' := y54_F_comm hH f hf f' hf'
  have hfa : Commute f a := y6b_comm_F_unit c hH hRT hf a ha
  have hfb : Commute f b := y6b_comm_F_unit c hH hRT hf b hb
  have haf' : Commute a f' := (y6b_comm_F_unit c hH hRT hf' a ha).symm
  have hab : Commute a b := y6b_unit_comm c hRT a ha b hb
  exact (Commute.mul_left (hff'.mul_right hfb) (haf'.mul_right hab)).eq

theorem y6b_E_sq (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) {x : G}
    (hx : x ∈ y6bE c) : x * x = 1 := by
  obtain ⟨f, hf, a, ha, rfl⟩ := y6bE_mem_form c hH hRT hx
  have hfa : Commute f a := y6b_comm_F_unit c hH hRT hf a ha
  rw [← pow_two, hfa.mul_pow 2, y54_F_sq hH f hf, y6b_unit_sq c hRT a ha, mul_one]

theorem y6b_E_le_T (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    y6bE c ≤ c.s.T := by
  rw [y6bE, y6bE16]
  apply sup_le
  · apply sup_le
    · exact (s3_F_le_A c.s).trans ((s3_A_le_S c.s).trans (c.s.S_le_R.trans c.s.R_le_T))
    · exact Subgroup.zpowers_le.mpr (y6b_g_mem_T c hRT)
  · exact Subgroup.zpowers_le.mpr (s3_t_mem_T c.s)

theorem y6b_E_le_H (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    y6bE c ≤ c.s.H :=
  (y6b_E_le_T c hH hRT).trans c.s.sylow_T.1

theorem y6b_card_E16 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    Nat.card ↥(y6bE16 c) = 16 := by
  have hg1 : c.g ≠ 1 := fun h => y6b_g_not_mem_F c hH hRT (h.symm ▸ c.s.fr.F.one_mem)
  have hgord : orderOf c.g = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using y6b_g_sq c hRT) hg1
  have hF8 : Nat.card ↥c.s.fr.F = 8 := by rw [(y54_F_isE3 hH).2]; norm_num
  have hgC : c.g ∈ Subgroup.centralizer (c.s.fr.F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact (y6b_g_comm_F c hH hRT f hf).symm
  have hnorm : Subgroup.zpowers c.g ≤ Subgroup.normalizer (c.s.fr.F : Set G) :=
    (Subgroup.zpowers_le.mpr hgC).trans (Subgroup.centralizer_le_normalizer _)
  have hdisj : Subgroup.zpowers c.g ⊓ c.s.fr.F = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxg, hxF⟩ := hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxg
    have hmod : n % (orderOf c.g : ℤ) = 0 ∨ n % (orderOf c.g : ℤ) = 1 := by
      rw [hgord]; exact Int.emod_two_eq_zero_or_one n
    rw [← zpow_mod_orderOf c.g n] at hxF ⊢
    rcases hmod with h2 | h2
    · rw [h2]; simp
    · exfalso
      apply y6b_g_not_mem_F c hH hRT
      rw [h2] at hxF
      simpa using hxF
  have hformula := y6e_card_sup_mul_inf (H := Subgroup.zpowers c.g) (N := c.s.fr.F) hnorm
  rw [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, hgord, hF8] at hformula
  rw [y6bE16, sup_comm, hformula]

theorem y6b_card_E (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    Nat.card ↥(y6bE c) = 32 := by
  have htord : orderOf c.s.t = 2 := c.s.t_order
  have htC : c.s.t ∈ Subgroup.centralizer (y6bE16 c : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact y6b_t_comm_E16 c hH hRT k hk
  have hnorm : Subgroup.zpowers c.s.t ≤ Subgroup.normalizer (y6bE16 c : Set G) :=
    (Subgroup.zpowers_le.mpr htC).trans (Subgroup.centralizer_le_normalizer _)
  have hdisj : Subgroup.zpowers c.s.t ⊓ y6bE16 c = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxt, hxE⟩ := hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxt
    have hmod : n % (orderOf c.s.t : ℤ) = 0 ∨ n % (orderOf c.s.t : ℤ) = 1 := by
      rw [htord]; exact Int.emod_two_eq_zero_or_one n
    rw [← zpow_mod_orderOf c.s.t n] at hxE ⊢
    rcases hmod with h2 | h2
    · rw [h2]; simp
    · exfalso
      apply y6b_t_not_mem_E16 c hH hRT
      rw [h2] at hxE
      simpa using hxE
  have hformula := y6e_card_sup_mul_inf (H := Subgroup.zpowers c.s.t) (N := y6bE16 c) hnorm
  rw [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, htord,
      y6b_card_E16 c hH hRT] at hformula
  rw [y6bE, sup_comm, hformula]

theorem y6b_E_inf_M3 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    y6bE c ⊓ M3 c.s = c.s.fr.F := by
  apply le_antisymm
  · calc y6bE c ⊓ M3 c.s ≤ c.s.H ⊓ M3 c.s := inf_le_inf (y6b_E_le_H c hH hRT) le_rfl
      _ = c.s.fr.F := y54_H_inf_M3 c hH
  · exact le_inf (y6b_F_le_E c) le_sup_right

end CFSG.OddStandard.HigherRank.YamadaG23
