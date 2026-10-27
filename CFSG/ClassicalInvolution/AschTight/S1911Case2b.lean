module

public import CFSG.ClassicalInvolution.AschTight.S1911C11

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G]

theorem conj_eq_inv_of_defect {R V : Subgroup G} (hVR : V ≤ R)
    (hcard : Nat.card R = 2 * Nat.card V) (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) {b : G}
    (hbR : b ∈ R) (hbV : b ∉ V) {a : G} (haR : a ∈ Subgroup.normalizer (R : Set G))
    (haV : a ∈ Subgroup.normalizer (V : Set G)) {u v : G} (hv : v ∈ V)
    (huV : ∀ x ∈ V, u * x = x * u) (hdef : b⁻¹ * (u * b * u⁻¹) = v)
    (hau : a * u * a⁻¹ = u⁻¹) : a * v * a⁻¹ = v⁻¹ := by
  obtain ⟨c, hc, hcdef⟩ : ∃ c ∈ V, b⁻¹ * (a * b * a⁻¹) = c :=
    ⟨_, inv_mul_conj_mem_of_normalizer hVR hcard hbR hbV haR haV, rfl⟩
  have hab : a * b * a⁻¹ = b * c := by rw [← hcdef]; group
  have hub : u * b * u⁻¹ = b * v := by rw [← hdef]; group
  have hvu : u * v = v * u := huV v hv
  have hub' : u⁻¹ * b * u = b * v⁻¹ := by
    have e : b = u⁻¹ * (b * v) * u := by rw [← hub]; group
    calc u⁻¹ * b * u = u⁻¹ * b * (u * v) * v⁻¹ := by group
      _ = u⁻¹ * b * (v * u) * v⁻¹ := by rw [hvu]
      _ = u⁻¹ * (b * v) * u * v⁻¹ := by group
      _ = b * v⁻¹ := by rw [← e]
  have hcu : u⁻¹ * c * u = c := by
    calc u⁻¹ * c * u = u⁻¹ * (c * u) := by group
      _ = u⁻¹ * (u * c) := by rw [huV c hc]
      _ = c := by group
  have h1 : a * (u * b * u⁻¹) * a⁻¹ = u⁻¹ * (a * b * a⁻¹) * u := by
    calc a * (u * b * u⁻¹) * a⁻¹ = (a * u * a⁻¹) * (a * b * a⁻¹) * (a * u * a⁻¹)⁻¹ := by group
      _ = u⁻¹ * (a * b * a⁻¹) * u := by rw [hau, inv_inv]
  rw [hub, hab] at h1
  have h2 : a * (b * v) * a⁻¹ = (a * b * a⁻¹) * (a * v * a⁻¹) := by group
  have h3 : u⁻¹ * (b * c) * u = (u⁻¹ * b * u) * (u⁻¹ * c * u) := by group
  rw [h2, hab, h3, hub', hcu] at h1
  have h4 : c * (a * v * a⁻¹) = v⁻¹ * c := by
    have h5 : b * (c * (a * v * a⁻¹)) = b * (v⁻¹ * c) := by
      simp only [mul_assoc] at h1 ⊢
      exact h1
    exact mul_left_cancel h5
  rw [hVc v⁻¹ (V.inv_mem hv) c hc] at h4
  exact mul_left_cancel h4

variable {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem exists_mul_mem_centralizer_of_comm (hd : Sec19DataT p f K z S W L t V) {s : G}
    (hsS : s ∈ (S : Subgroup G)) (hsU : ∀ u ∈ K ⊓ W, s * u = u * s) :
    ∃ c ∈ V, s * c⁻¹ ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  have hd0 := hd.toSec19Data
  have hcomm := comm_of_mem hd0
  have hUR : K ⊓ W ≤ (S : Subgroup G) ⊓ K := fun x hx => ⟨hd.hWS hx.2, hx.1⟩
  have hcard := card_inf_eq hd0
  obtain ⟨b, hbR, hbU⟩ := exists_mem_not_mem hcard
  have hdef := inv_mul_conj_mem hUR hcard hbR (le_normalizer_inf hd0 hsS) hsU
  have hVR : V ≤ Subgroup.normalizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
    fun v hv => le_normalizer_inf hd0 (hd.hWS (hd.leW hv))
  have hdisj : V ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) = ⊥ := by
    rw [eq_bot_iff, ← inf_sec19Y_eq_bot hd]
    rintro x ⟨hxV, hxC⟩
    have hx : x ∈ W ⊓ sec19Y K z := by
      rw [inf_sec19Y_eq hd0]
      exact ⟨hd.leW hxV, hxC⟩
    exact ⟨hxV, hx.2⟩
  obtain ⟨c, hcV, hc⟩ := exists_defect_eq hUR hcard (C := V) hVR
    (fun c hc u hu => hcomm c (hd.leW hc) u hu.2) hdisj (card_inf_eq_card hd).le hbR hbU hdef
  exact ⟨c, hcV, mem_centralizer_of_defect_eq hUR hcard hbR hbU (hVR hcV) hsU
    (fun u hu => hcomm c (hd.leW hcV) u hu.2) hc.symm⟩

theorem inf_centralizer_W_eq (h11b : C19_11bTmp p f) (hd : Sec19DataT p f K z S W L t V) :
    (S : Subgroup G) ⊓ Subgroup.centralizer (W : Set G) = W := by
  have hcomm := comm_of_mem hd.toSec19Data
  apply le_antisymm
  · rintro s ⟨hsS, hsW⟩
    obtain ⟨c, hcV, hc⟩ := exists_mul_mem_centralizer_of_comm hd hsS
      (fun u hu => (Subgroup.mem_centralizer_iff.mp hsW u hu.2).symm)
    have hcW : c⁻¹ ∈ Subgroup.centralizer (W : Set G) :=
      Subgroup.inv_mem _ (Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx c (hd.leW hcV))
    have h := mem_W_of_c19_11b h11b hd ((S : Subgroup G).mul_mem hsS
      ((S : Subgroup G).inv_mem (hd.hWS (hd.leW hcV)))) hc (Subgroup.mul_mem _ hsW hcW)
    have e : s = s * c⁻¹ * c := by group
    rw [e]
    exact W.mul_mem h (hd.leW hcV)
  · exact le_inf hd.hWS fun w hw => Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx w hw

theorem comm_V_of_comm_U (hd : Sec19DataT p f K z S W L t V) {a : G}
    (haS : a ∈ (S : Subgroup G)) (hat : a ∈ Subgroup.centralizer ({t} : Set G))
    (haU : ∀ u ∈ K ⊓ W, a * u = u * a) : ∀ v ∈ V, a * v = v * a := by
  obtain ⟨RL, hRL, haRL, hWRL, hVRL, hcardRL⟩ := exists_sylow_member_of_mem_A hd haS hat
  obtain ⟨b, hbR, hbV⟩ := exists_mem_not_mem hcardRL
  have hcomm := comm_of_mem hd.toSec19Data
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    hcomm x (hd.leW hx) y (hd.leW hy)
  intro v hv
  obtain ⟨u, hu, hdef⟩ := exists_defect_eq hVRL hcardRL (C := K ⊓ W)
    (fun x hx => mem_normalizer_iff_conjSub_eq.mpr (hWRL x hx.2))
    (fun x hx y hy => hcomm x hx.2 y (hd.leW hy)) (inf_inf_centralizer_eq_bot hd hRL)
    (card_inf_eq_card hd).ge hbR hbV hv
  have h := conj_eq_of_defect hVRL hcardRL hVc hbR hbV (mem_normalizer_iff_conjSub_eq.mpr haRL)
    (mem_normalizer_V_of_mem_A hd haS hat) hv (fun x hx => hcomm u hu.2 x (hd.leW hx)) hdef
    (haU u hu)
  calc a * v = a * v * a⁻¹ * a := by group
    _ = v * a := by rw [h]

theorem mem_W_of_comm_U (h11b : C19_11bTmp p f) (hd : Sec19DataT p f K z S W L t V) {a : G}
    (haS : a ∈ (S : Subgroup G)) (hat : a ∈ Subgroup.centralizer ({t} : Set G))
    (haU : ∀ u ∈ K ⊓ W, a * u = u * a) : a ∈ W := by
  have haV := comm_V_of_comm_U hd haS hat haU
  have haW : a ∈ Subgroup.centralizer (W : Set G) := by
    have h := mem_centralizer_sup_of (H₁ := K ⊓ W) (H₂ := V)
      (Subgroup.mem_centralizer_iff.mpr fun u hu => (haU u hu).symm)
      (Subgroup.mem_centralizer_iff.mpr fun v hv => (haV v hv).symm)
    rwa [← sup_eq_inf_sup hd] at h
  exact (inf_centralizer_W_eq h11b hd).le ⟨haS, haW⟩

theorem inv_V_of_inv_U (hd : Sec19DataT p f K z S W L t V) {a : G} (haS : a ∈ (S : Subgroup G))
    (hat : a ∈ Subgroup.centralizer ({t} : Set G))
    (haU : ∀ u ∈ K ⊓ W, a * u * a⁻¹ = u⁻¹) : ∀ v ∈ V, a * v * a⁻¹ = v⁻¹ := by
  obtain ⟨RL, hRL, haRL, hWRL, hVRL, hcardRL⟩ := exists_sylow_member_of_mem_A hd haS hat
  obtain ⟨b, hbR, hbV⟩ := exists_mem_not_mem hcardRL
  have hcomm := comm_of_mem hd.toSec19Data
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    hcomm x (hd.leW hx) y (hd.leW hy)
  intro v hv
  obtain ⟨u, hu, hdef⟩ := exists_defect_eq hVRL hcardRL (C := K ⊓ W)
    (fun x hx => mem_normalizer_iff_conjSub_eq.mpr (hWRL x hx.2))
    (fun x hx y hy => hcomm x hx.2 y (hd.leW hy)) (inf_inf_centralizer_eq_bot hd hRL)
    (card_inf_eq_card hd).ge hbR hbV hv
  exact conj_eq_inv_of_defect hVRL hcardRL hVc hbR hbV (mem_normalizer_iff_conjSub_eq.mpr haRL)
    (mem_normalizer_V_of_mem_A hd haS hat) hv (fun x hx => hcomm u hu.2 x (hd.leW hx)) hdef
    (haU u hu)

theorem inv_W_of_inv_U (hd : Sec19DataT p f K z S W L t V) {a : G} (haS : a ∈ (S : Subgroup G))
    (hat : a ∈ Subgroup.centralizer ({t} : Set G))
    (haU : ∀ u ∈ K ⊓ W, a * u * a⁻¹ = u⁻¹) : ∀ w ∈ W, a * w * a⁻¹ = w⁻¹ := by
  have hV := inv_V_of_inv_U hd haS hat haU
  have hcomm := comm_of_mem hd.toSec19Data
  let H : Subgroup G :=
    { carrier := {w | w ∈ W ∧ a * w * a⁻¹ = w⁻¹}
      one_mem' := ⟨W.one_mem, by group⟩
      mul_mem' := fun {x y} hx hy => ⟨W.mul_mem hx.1 hy.1, by
        calc a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
          _ = x⁻¹ * y⁻¹ := by rw [hx.2, hy.2]
          _ = (x * y)⁻¹ := by
            rw [mul_inv_rev]
            exact hcomm _ (W.inv_mem hx.1) _ (W.inv_mem hy.1)⟩
      inv_mem' := fun {x} hx => ⟨W.inv_mem hx.1, by
        calc a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
          _ = x⁻¹⁻¹ := by rw [hx.2]⟩ }
  have hle : W ≤ H := by
    conv_lhs => rw [sup_eq_inf_sup hd]
    exact sup_le (fun u hu => ⟨hu.2, haU u hu⟩) (fun v hv => ⟨hd.leW hv, hV v hv⟩)
  exact fun w hw => (hle hw).2

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
