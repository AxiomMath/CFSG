module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Fusion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Sq

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

section Generic

variable {G : Type*} [Group G]

theorem exists_pow_four_of_cyclic [Finite G] {F : Subgroup G} (hF : IsCyclic ↥F)
    (hF2 : IsPGroup 2 F) (h4 : 4 ≤ Nat.card F) : ∃ w ∈ F, w ^ 4 = 1 ∧ w ^ 2 ≠ 1 := by
  obtain ⟨e, he⟩ := hF2.exists_card_eq
  have he2 : 2 ≤ e := by
    by_contra h
    have h1 : e ≤ 1 := by omega
    have h2 : 2 ^ e ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
    omega
  obtain ⟨g, hg⟩ := hF.exists_generator
  have hord : orderOf g = Nat.card F := orderOf_eq_card_of_forall_mem_zpowers hg
  have h4dvd : 4 ∣ Nat.card F := by
    rw [he]
    exact ⟨2 ^ (e - 2), by rw [show e = 2 + (e - 2) by omega, pow_add]; simp⟩
  have hm4 : Nat.card F / 4 * 4 = Nat.card F := Nat.div_mul_cancel h4dvd
  have hpos : 0 < Nat.card F := Nat.card_pos
  refine ⟨(g : G) ^ (Nat.card F / 4), F.pow_mem g.2 _, ?_, ?_⟩
  · rw [← pow_mul, hm4]
    have h1 : g ^ Nat.card F = 1 := pow_card_eq_one'
    calc (g : G) ^ Nat.card F = ((g ^ Nat.card F : F) : G) := (SubmonoidClass.coe_pow g (Nat.card F)).symm
      _ = 1 := by rw [h1]; rfl
  · rw [← pow_mul]
    have : Nat.card F / 4 * 2 < orderOf (g : G) := by
      rw [Subgroup.orderOf_coe, hord]; omega
    exact pow_ne_one_of_lt_orderOf (by omega) this

theorem not_exists_sq_two_pow_of_odd {m : ℕ} (hm : Odd m) : ¬ ∃ d : ℕ, 2 ^ m = d ^ 2 := by
  rintro ⟨d, hd⟩
  have hdvd : d ∣ 2 ^ m := by rw [hd]; exact Dvd.intro_left _ (pow_two d).symm
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have h1 : 2 ^ m = 2 ^ (a * 2) := by rw [hd, ← pow_mul]
  have h2 := Nat.pow_right_injective (le_refl 2) h1
  obtain ⟨k, hk⟩ := hm
  omega

end Generic

namespace Lin2Hyp

section Core

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem card_S_eq {F : Subgroup G} (hFS : F ≤ S) (hRF : thompsonJ S ⊓ F = ⊥)
    (hRFS : thompsonJ S ⊔ F = S) :
    Nat.card S = Nat.card (thompsonJ S) * Nat.card F := by
  have hSR : S ≤ Subgroup.normalizer (thompsonJ S : Set G) := hcfg.S_le_T.trans (E.TnR hcfg)
  have h := card_sup_mul_card_inf (A := F) (B := thompsonJ S) (hFS.trans hSR)
  rw [sup_comm, hRFS, inf_comm, hRF, Subgroup.card_bot, mul_one] at h
  rw [h, mul_comm]

theorem card_T_eq : Nat.card T = 2 * Nat.card S := by
  rw [card_eq_mul_of_relIndex hcfg.S_le_T, E.idxTS hcfg, mul_comm]

theorem card_T_mul_Rs {s : G} (hs : s ∈ S) (hsR : s ∉ thompsonJ S) (hs2 : s ^ 2 = 1) :
    Nat.card T * Nat.card (thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) =
      Nat.card (T ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) *
        Nat.card (thompsonJ S) := by
  have hRT : thompsonJ S ≤ T := (thompsonJ_le_self S).trans hcfg.S_le_T
  have h := card_sup_mul_card_inf (A := T ⊓ Subgroup.centralizer ({s} : Set G))
    (B := thompsonJ S) (inf_le_left.trans (E.TnR hcfg))
  rw [sup_comm, ← E.T_eq_sup_centralizer hcfg hs hsR hs2] at h
  have e : T ⊓ Subgroup.centralizer ({s} : Set G) ⊓ thompsonJ S =
      thompsonJ S ⊓ Subgroup.centralizer ({s} : Set G) := by
    ext y
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨_, hy⟩, hyR⟩
      exact ⟨hyR, hy⟩
    · rintro ⟨hyR, hy⟩
      exact ⟨⟨hRT hyR, hy⟩, hyR⟩
  rw [e] at h
  exact h

theorem false_of_odd (hc : centerOf L ≠ ⊥) (hodd : Odd (n / 2)) : False := by
  obtain ⟨f₀, hf₀S, hf₀R, hf₀2, hev, hconj, -⟩ := E.exists_f₀ hcfg
  obtain ⟨F, hFcyc, hFS, hRF, hRFS, -⟩ := E.exists_F hcfg
  have hF2 : IsPGroup 2 F := hcfg.S_isPGroup.to_le hFS
  have hRT : thompsonJ S ≤ T := (thompsonJ_le_self S).trans hcfg.S_le_T
  have hTR : T ≤ Subgroup.normalizer (thompsonJ S : Set G) := E.TnR hcfg
  have hFle : Nat.card F ≤ 2 := by
    by_contra hlt
    obtain ⟨e, he⟩ := hF2.exists_card_eq
    have h4 : 4 ≤ Nat.card F := by
      by_contra h4
      have he1 : e ≤ 1 := by
        by_contra h
        have : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have : 2 ^ e ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) he1
      omega
    obtain ⟨w, hwF, hw4, hw2⟩ := exists_pow_four_of_cyclic hFcyc hF2 h4
    have hs'S : w ^ 2 ∈ S := S.pow_mem (hFS hwF) 2
    have hs'R : w ^ 2 ∉ thompsonJ S := by
      intro h
      have : w ^ 2 ∈ thompsonJ S ⊓ F := ⟨h, F.pow_mem hwF 2⟩
      rw [hRF, Subgroup.mem_bot] at this
      exact hw2 this
    have hs'2 : (w ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hw4
    obtain ⟨hZe, hZcard, hZS⟩ := E.Zbasic hcfg (Z := lin2Z L (thompsonJ S)) rfl
    have hCZ := E.card_Z_inf_centralizer hcfg (Z := lin2Z L (thompsonJ S)) rfl hs'S hs'R hs'2
    obtain ⟨m, hm⟩ := hev
    have hcard : Nat.card (lin2Z L (thompsonJ S)) =
        Nat.card (lin2Z L (thompsonJ S) ⊓ Subgroup.centralizer ({w ^ 2} : Set G) :
          Subgroup G) ^ 2 := by
      rw [hZcard, hCZ, ← pow_mul]
      congr 1
      omega
    obtain ⟨d, hd⟩ := exists_sq_card_inf_centralizer_sq hZe (hZS (hFS hwF)) hw4 hcard
    rw [hCZ] at hd
    exact not_exists_sq_two_pow_of_odd hodd ⟨d, hd⟩
  have hFne : Nat.card F ≠ 1 := by
    intro h1
    have : F = ⊥ := Subgroup.card_eq_one.mp h1
    rw [this, sup_bot_eq] at hRFS
    exact (E.R_lt_S hcfg).ne hRFS
  have hF2c : Nat.card F = 2 := by
    have := Nat.card_pos (α := F)
    omega
  have hSc : Nat.card S = 2 * Nat.card (thompsonJ S) := by
    rw [E.card_S_eq hcfg hFS hRF hRFS, hF2c, mul_comm]
  have hTc : Nat.card T = 4 * Nat.card (thompsonJ S) := by
    rw [E.card_T_eq hcfg, hSc]; ring
  obtain ⟨B, hB⟩ := E.exists_B hcfg
  have hRTB : thompsonJ S ⊔ (T ⊓ Subgroup.normalizer (B : Set G)) = T :=
    hB.2.2.2.2.2.2.2.2.1
  have hRTB' : thompsonJ S ⊓ (T ⊓ Subgroup.normalizer (B : Set G)) = ⊥ :=
    hB.2.2.2.2.2.2.2.2.2.1
  set TB := T ⊓ Subgroup.normalizer (B : Set G) with hTB
  have hTBcard : Nat.card TB = 4 := by
    have h := card_sup_mul_card_inf (A := TB) (B := thompsonJ S) (inf_le_left.trans hTR)
    rw [sup_comm, hRTB, inf_comm, hRTB', Subgroup.card_bot, mul_one, hTc] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card (thompsonJ S))
      (by rw [mul_comm, h]; ring)
  have hsq : ∀ b ∈ TB, b ^ 2 = 1 := by
    intro b hb
    by_contra hb2
    have hdvd : orderOf b ∣ 2 ^ 2 := by
      have := orderOf_dvd_natCard (⟨b, hb⟩ : TB)
      rw [hTBcard, Subgroup.orderOf_mk] at this
      simpa using this
    obtain ⟨k, hk, hbk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hk2 : k = 2 := by
      by_contra hk2
      have hk1 : k ≤ 1 := by omega
      apply hb2
      apply orderOf_dvd_iff_pow_eq_one.1
      rw [hbk]
      calc 2 ^ k ∣ 2 ^ 1 := pow_dvd_pow 2 hk1
        _ = 2 := by norm_num
    have hord4 : orderOf b = 4 := by rw [hbk, hk2]; norm_num
    have hzp : Subgroup.zpowers b = TB :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hb)
        (by rw [Nat.card_zpowers, hord4, hTBcard])
    exact E.TR_not_cyclic hcfg ⟨b, hb.1, by rw [hzp]; exact hRTB.symm⟩
  obtain ⟨x, hxTB, hxS⟩ : ∃ x ∈ TB, x ∉ S := by
    by_contra hne
    have hTBS : TB ≤ S := fun y hy => by_contra fun hyS => hne ⟨y, hy, hyS⟩
    have : T ≤ S := by rw [← hRTB]; exact sup_le (thompsonJ_le_self S) hTBS
    exact hcfg.S_ne_T (le_antisymm hcfg.S_le_T this)
  have hxT : x ∈ T := hxTB.1
  have hx2 : x ^ 2 = 1 := hsq x hxTB
  have hTBcomm : ∀ a ∈ TB, ∀ b ∈ TB, a * b = b * a := by
    intro a ha b hb
    have h1 := hsq (a * b) (TB.mul_mem ha hb)
    have h2 := hsq a ha
    have h3 := hsq b hb
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h2)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h3)
    have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h1)
    calc a * b = (a * b)⁻¹ := hab.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [ha', hb']
  have hcomm : ∀ a ∈ T, ∀ b ∈ T, a⁻¹ * b⁻¹ * a * b ∈ thompsonJ S :=
    commutator_mem_of_sup_commutative hTR inf_le_left hRTB hTBcomm
  have hsqR : x ^ 2 ∈ thompsonJ S := by rw [hx2]; exact one_mem _
  obtain ⟨-, htrans, hcases⟩ := E.h14 G T M H S L D n hcfg x hxT hxS hsqR
  rcases hcases hx2 with ⟨hc', -⟩ | ⟨hc', -⟩ | ⟨-, hcardR, hcardΩ⟩
  · exact hc hc'
  · exact hc hc'
  have hfus : ∀ g : G, g⁻¹ * x * g ∉ S := by
    intro g hgS
    have hy2 : (g⁻¹ * x * g) ^ 2 = 1 := by
      have : (g⁻¹ * x * g) ^ 2 = g⁻¹ * x ^ 2 * g := by simp only [pow_two]; group
      rw [this, hx2]; simp
    have e : (g⁻¹)⁻¹ * (g⁻¹ * x * g) * g⁻¹ = x := by group
    by_cases hgR : g⁻¹ * x * g ∈ thompsonJ S
    · have := (E.h21 G T M H S L D n hcfg).2 (g⁻¹ * x * g) hgR hy2 g⁻¹ (by rw [e]; exact hxT)
      rw [e] at this
      exact hxS (thompsonJ_le_self S this)
    · refine E.not_conj_of_card hcfg hgS hgR hy2 hx2 (fun g' hg' => hcomm x hxT g' hg') htrans
        ?_ ?_ g⁻¹ e
      · rw [hcardR, (E.card_R_inf_centralizer hcfg hgS hgR hy2).2 hc]
      · rw [hcardΩ, ((E.U_s_values hcfg hgS hgR hy2 hxT hxS).2 hc).1]
        exact Nat.pow_lt_pow_right (by norm_num) (by have := hcfg.one_lt; omega)
  have hcycT : T = S ⊔ Subgroup.zpowers x := by
    apply le_antisymm
    · intro k hk
      by_cases hkS : k ∈ S
      · exact Subgroup.mem_sup_left hkS
      · have h1 : x⁻¹ * k ∈ S := inv_mul_mem_of_relIndex_two (E.idxTS hcfg) hxT hk hxS hkS
        have e : k = x * (x⁻¹ * k) := by group
        rw [e]
        exact (S ⊔ Subgroup.zpowers x).mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
          (Subgroup.mem_sup_left h1)
    · exact sup_le hcfg.S_le_T (Subgroup.zpowers_le.2 hxT)
  have : IsSimpleGroup G := hcfg.simple
  exact transfer_contradiction_cyclic hcfg.nonabelian hcfg.sylowT hcfg.S_le_T (E.TnS hcfg) hcycT
    hxT hxS hx2 hfus

theorem false_of_even (h5 : Lemma2_4_23_five) (hc : centerOf L ≠ ⊥) (heven : Even (n / 2)) :
    False := by
  obtain ⟨f₀, hf₀S, hf₀R, hf₀2, hev, hconj, -⟩ := E.exists_f₀ hcfg
  have hn := hcfg.one_lt
  have hRS : thompsonJ S ≤ S := thompsonJ_le_self S
  have hST : S ≤ T := hcfg.S_le_T
  have hRT : thompsonJ S ≤ T := hRS.trans hST
  have hTR : T ≤ Subgroup.normalizer (thompsonJ S : Set G) := E.TnR hcfg
  have hSR : S ≤ Subgroup.normalizer (thompsonJ S : Set G) := hST.trans hTR
  obtain ⟨a, ha⟩ := hev
  obtain ⟨b, hb⟩ := heven
  have h4n : 4 ∣ n := ⟨b, by omega⟩
  have hn4 : 4 ≤ n := by omega
  have h4lt : 4 < 2 ^ n := by
    have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn4
    omega
  have hν : 2 ≤ n.factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by omega)).mp (by simpa using h4n)
  obtain ⟨x₀, hx₀, hx₀S⟩ := E.exists_mem_T_centralizer_not_mem_S hcfg hf₀S hf₀R hf₀2
  obtain ⟨-, -, ⟨t, htTs, hTseq⟩, hidx⟩ :=
    h5 G T M H S L D n hcfg f₀ hf₀S hf₀R hf₀2 hc h4lt x₀ hx₀ hx₀S
  obtain ⟨F, hFcyc, hFS, hRF, hRFS, -⟩ := E.exists_F hcfg
  have hF2 : IsPGroup 2 F := hcfg.S_isPGroup.to_le hFS
  set R := thompsonJ S with hR
  set C := Subgroup.centralizer ({f₀} : Set G) with hC
  have hf₀1 : f₀ ≠ 1 := fun h => hf₀R (h ▸ R.one_mem)
  have hf₀C : f₀ ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hFcard : 4 ≤ Nat.card F := by
    set J : Subgroup G := Subgroup.zpowers f₀ ⊔ R ⊓ C with hJ
    have hJle : J ≤ T ⊓ C := by rw [hTseq]; exact le_sup_left
    have hJcard : Nat.card (T ⊓ C : Subgroup G) = Nat.card J * 2 ^ n.factorization 2 := by
      rw [card_eq_mul_of_relIndex hJle, hidx]
    have hsN : f₀ ∈ Subgroup.normalizer ((R ⊓ C : Subgroup G) : Set G) := by
      rw [← conjR_eq_self_iff, conjR_inf, conjR_eq_of_mem_normalizer (hSR hf₀S),
        conjR_eq_of_mem hf₀C]
    have hbot : Subgroup.zpowers f₀ ⊓ (R ⊓ C) = ⊥ := by
      rw [eq_bot_iff]
      intro y ⟨hy1, hy2⟩
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy1
      rcases zpow_of_sq_eq_one hf₀2 j with h | h
      · rw [h]; exact one_mem _
      · exact absurd (h ▸ hy2.1) hf₀R
    have hz : Nat.card (Subgroup.zpowers f₀) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime hf₀2 hf₀1
    have hJ2 : Nat.card J = 2 * Nat.card (R ⊓ C : Subgroup G) := by
      have h := card_sup_mul_card_inf (A := Subgroup.zpowers f₀) (B := R ⊓ C)
        (Subgroup.zpowers_le.2 hsN)
      rw [hbot, Subgroup.card_bot, mul_one, hz] at h
      exact h
    have hT := E.card_T_mul_Rs hcfg hf₀S hf₀R hf₀2
    have hSc := E.card_S_eq hcfg hFS hRF hRFS
    have hTc := E.card_T_eq hcfg
    have hRspos : 0 < Nat.card (R ⊓ C : Subgroup G) := Nat.card_pos
    have hRpos : 0 < Nat.card R := Nat.card_pos
    have h1 : Nat.card T = 2 * 2 ^ n.factorization 2 * Nat.card R := by
      apply Nat.eq_of_mul_eq_mul_right hRspos
      rw [hT, hJcard, hJ2]
      ring
    have h2 : Nat.card F = 2 ^ n.factorization 2 := by
      have hS' : Nat.card S = 2 ^ n.factorization 2 * Nat.card R := by
        apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
        rw [← hTc, h1]; ring
      apply Nat.eq_of_mul_eq_mul_left hRpos
      rw [← hSc, hS']; ring
    rw [h2]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n.factorization 2 := Nat.pow_le_pow_right (by norm_num) hν
  obtain ⟨w, hwF, hw4, hw2⟩ := exists_pow_four_of_cyclic hFcyc hF2 hFcard
  have hy₀S : w ^ 2 ∈ S := S.pow_mem (hFS hwF) 2
  have hy₀R : w ^ 2 ∉ R := by
    intro h
    have : w ^ 2 ∈ R ⊓ F := ⟨h, F.pow_mem hwF 2⟩
    rw [hRF, Subgroup.mem_bot] at this
    exact hw2 this
  have hy₀2 : (w ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hw4
  obtain ⟨c₂, hc₂, hc₂e⟩ := hconj (w ^ 2) hy₀S hy₀R hy₀2
  have htT : t ∈ T := htTs.1
  have hts : t * f₀ = f₀ * t := Subgroup.mem_centralizer_singleton_iff.mp htTs.2
  set K := R ⊔ Subgroup.zpowers t with hK
  have hRK : R ≤ K := le_sup_left
  have htK : t ∈ K := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hconjK : ∀ g ∈ Subgroup.normalizer (R : Set G), g * t = t * g →
      ∀ y ∈ K, g * y * g⁻¹ ∈ K := by
    intro g hg hgt y hy
    obtain ⟨r, hr, u, hu, rfl⟩ :=
      (mem_sup_iff_of_le_normalizer (Subgroup.zpowers_le.2 (hTR htT))).1 hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    have h1 : g * t ^ j * g⁻¹ = t ^ j := by
      have : g * t ^ j = t ^ j * g := ((Commute.zpow_right (show Commute g t from hgt) j)).eq
      rw [this, mul_inv_cancel_right]
    have e : g * (r * t ^ j) * g⁻¹ = (g * r * g⁻¹) * (g * t ^ j * g⁻¹) := by group
    rw [e, h1]
    exact K.mul_mem (hRK ((Subgroup.mem_normalizer_iff.mp hg r).mp hr))
      (Subgroup.zpow_mem K htK j)
  have hcommt : ∀ g ∈ Subgroup.zpowers f₀, g * t = t * g := by
    intro g hg
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact ((Commute.zpow_left (show Commute f₀ t from hts.symm) j)).eq
  have hsN : Subgroup.zpowers f₀ ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_conj_mem fun g hg y hy =>
      hconjK g ((Subgroup.zpowers_le.2 (hSR hf₀S)) hg) (hcommt g hg) y hy
  have hTle : T ≤ K ⊔ Subgroup.zpowers f₀ := by
    have hTeq := E.T_eq_sup_centralizer hcfg hf₀S hf₀R hf₀2
    rw [hTeq]
    refine sup_le (hRK.trans le_sup_left) ?_
    rw [hTseq]
    refine sup_le (sup_le le_sup_right (inf_le_left.trans (hRK.trans le_sup_left))) ?_
    exact (Subgroup.zpowers_le.2 htK).trans le_sup_left
  have hw2K : w ^ 2 ∈ K := by
    have hwT : w ∈ K ⊔ Subgroup.zpowers f₀ := hTle (hST (hFS hwF))
    obtain ⟨k, hk, h, hh, hwe⟩ := (mem_sup_iff_of_le_normalizer hsN).1 hwT
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    rcases zpow_of_sq_eq_one hf₀2 j with h1 | h1
    · rw [h1, mul_one] at hwe
      rw [hwe]
      exact K.pow_mem hk 2
    · rw [h1] at hwe
      have hff : f₀ * f₀ = 1 := by simpa [pow_two] using hf₀2
      have e : w ^ 2 = k * (f₀ * k * f₀⁻¹) := by
        calc w ^ 2 = (k * f₀) * (k * f₀) := by rw [hwe, pow_two]
          _ = k * (f₀ * k * f₀⁻¹) * (f₀ * f₀) := by group
          _ = k * (f₀ * k * f₀⁻¹) := by rw [hff, mul_one]
      rw [e]
      exact K.mul_mem hk (hconjK f₀ (hSR hf₀S) hts.symm k hk)
  have hf₀K : f₀ ∈ K := by
    have e : f₀ = c₂ * (w ^ 2) * c₂⁻¹ := by rw [← hc₂e]; group
    rw [e]
    exact K.mul_mem (K.mul_mem (hRK hc₂) hw2K) (K.inv_mem (hRK hc₂))
  have hTK : T = K := by
    apply le_antisymm
    · refine hTle.trans (sup_le le_rfl (Subgroup.zpowers_le.2 hf₀K))
    · exact sup_le hRT (Subgroup.zpowers_le.2 htT)
  exact E.TR_not_cyclic hcfg ⟨t, htT, hTK⟩

end Core

end Lin2Hyp

theorem lemma2_4_24_core_of (E : Lin2Hyp) (h5 : Lemma2_4_23_five) : Lemma2_4_24_core := by
  intro G _ _ T M H S L D n hcfg
  by_contra hc
  rcases Nat.even_or_odd (n / 2) with h | h
  · exact E.false_of_even hcfg h5 hc h
  · exact E.false_of_odd hcfg hc h

theorem lin2_core_and_fusion (h8 : Lemma2_4_8) (h11 : Lemma2_4_11) (h12 : Lemma2_4_12)
    (h14 : Lemma2_4_14) (h21 : Lemma2_4_21_core) (h5 : Lemma2_4_23_five) :
    Lemma2_4_24_core ∧ Lemma2_4_s1_fusion :=
  have core := lemma2_4_24_core_of ⟨h8, h11, h12, h14, h21⟩ h5
  ⟨core, lemma2_4_s1_fusion_of ⟨h8, h11, h12, h14, h21⟩ core⟩

end CFSG.QuasithinUnique.Lin2
