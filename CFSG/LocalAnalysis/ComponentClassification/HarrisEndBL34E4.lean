module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Fuse
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Graph

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

theorem EndB.eq_one_or_eq_of_mem_zpowers_sq {G : Type*} [Group G] {u x : G} (hu : u ^ 2 = 1)
    (hx : x ∈ zpowers u) : x = 1 ∨ x = u := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_ofNat, hu, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_ofNat, hu, one_zpow, one_mul, zpow_one]

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

theorem EndB.exists_conj_xt (hKF : AutPSL2FusionInput) (hs : Setting46e t L p f S w z V i j)
    (hzM : z ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
    (m : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (hm : m * hs.setup.tBar i j * m⁻¹ = QuotientGroup.mk ⟨z, hzM⟩ * hs.setup.tBar i j)
    {x : X} (hxD : x ∈ S ⊓ L) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
    ∃ c : X, c * t * c⁻¹ = x * t := by
  have htM := hs.setup.t_mem_centralizer_beta i j
  have htS : t ∈ S := hs.setup.T_le (mem_sup_left (mem_sup_left (mem_zpowers t)))
  have hzt : z * t = t * z := hs.setup.z_comm htS |>.symm
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hzt2 : (z * t) ^ 2 = 1 := by
    rw [(show Commute z t from hzt).mul_pow, hz2, ht2, one_mul]
  obtain ⟨g', hg'⟩ := QuotientGroup.mk_surjective m
  set N := (pPrimeCore 2 ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))).map
    (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)).subtype with hN
  have hNodd : Odd (Nat.card N) := Nat.coprime_two_left.mp (coprime_card_map_pPrimeCore _)
  have hcoset : ((g' : X) * t * (g' : X)⁻¹)⁻¹ * (z * t) ∈ N := by
    have h1 : (QuotientGroup.mk ((g' * ⟨t, htM⟩ * g'⁻¹)⁻¹ * (⟨z, hzM⟩ * ⟨t, htM⟩)) :
        MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_mul]
      change ((g' : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * hs.setup.tBar i j *
        (g' : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))⁻¹)⁻¹ *
        (QuotientGroup.mk ⟨z, hzM⟩ * hs.setup.tBar i j) = 1
      rw [hg', hm, inv_mul_cancel]
    rw [QuotientGroup.eq_one_iff] at h1
    exact ⟨_, h1, rfl⟩
  have hx₀2 : ((g' : X) * t * (g' : X)⁻¹) ^ 2 = 1 := by
    rw [sq, show (g' : X) * t * (g' : X)⁻¹ * ((g' : X) * t * (g' : X)⁻¹) =
      (g' : X) * (t * t) * (g' : X)⁻¹ by group, ← sq t, ht2, mul_one, mul_inv_cancel]
  obtain ⟨n₀, -, hn₀⟩ := exists_conj_of_mem_coset_odd hNodd hx₀2 hzt2 hcoset
  obtain ⟨g₁, hg₁H, hg₁⟩ := hs.setup.exists_conj_eq_z hKF hxD hx2 hx1
  refine ⟨g₁⁻¹ * (n₀ * g'), ?_⟩
  have hg₁t : g₁⁻¹ * t * g₁ = t := by
    rw [mul_assoc, ← mem_centralizer_singleton_iff.mp hg₁H]
    group
  have hg₁x : g₁⁻¹ * z * g₁ = x := by rw [← hg₁]; group
  calc g₁⁻¹ * (n₀ * g') * t * (g₁⁻¹ * (n₀ * g'))⁻¹
      = g₁⁻¹ * (n₀ * ((g' : X) * t * (g' : X)⁻¹) * n₀⁻¹) * g₁ := by group
    _ = g₁⁻¹ * (z * t) * g₁ := by rw [hn₀]
    _ = (g₁⁻¹ * z * g₁) * (g₁⁻¹ * t * g₁) := by group
    _ = x * t := by rw [hg₁x, hg₁t]

namespace EndB.LLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* PSL3Four.S}

theorem false_of_conj_xt
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput)
    (hUC : GrSLit.L34UnitaryCentralizerFact) (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (hQE : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    {x : X} (hxD : x ∈ S ⊓ L) (hx2 : x ^ 2 = 1)
    (hxM : x ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
    (h0 : ((hL.rho (QuotientGroup.mk ⟨x, hxM⟩) : PSL3Four.R) : Equiv.Perm (Fin 42)) ∉
      PSL3Four.S)
    (h1 : ((hL.rho (QuotientGroup.mk ⟨x, hxM⟩ * hs.setup.tBar i j) : PSL3Four.R) :
      Equiv.Perm (Fin 42)) ∉ PSL3Four.S) {c : X} (hc : c * t * c⁻¹ = x * t) : False := by
  have htM := hs.setup.t_mem_centralizer_beta i j
  have hτM : c * t * c⁻¹ ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) := by
    rw [hc]
    exact mul_mem hxM htM
  have htb : hs.setup.tBar i j = (QuotientGroup.mk ⟨t, htM⟩ :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := rfl
  have hτb : (QuotientGroup.mk ⟨c * t * c⁻¹, hτM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      QuotientGroup.mk ⟨x, hxM⟩ * hs.setup.tBar i j := by
    rw [htb, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hc
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq]; exact pow_orderOf_eq_one t
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp
    (hs.standing.config.le_centralizer (mem_inf.mp hxD).2)
  have hxb2 := EndB.mk_sq hxM hx2
  have hxbt : (QuotientGroup.mk ⟨x, hxM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) *
      hs.setup.tBar i j = hs.setup.tBar i j * QuotientGroup.mk ⟨x, hxM⟩ :=
    EndB.mk_comm hxM htM hxt
  obtain ⟨-, hrtS⟩ := hL.rho_t_facts
  rcases hL.graph_unitary hxb2 hxbt h0 h1 with ⟨-, ⟨d, hd, hdu⟩⟩ | ⟨-, ⟨d, hd, hdg⟩⟩
  ·
    refine hL.false_of_conj_unitary hKF hUC hZ hQE c hτM hd (by rw [hτb]; exact hdu)
      (a := QuotientGroup.mk ⟨x, hxM⟩) (b := hs.setup.tBar i j) ?_ ?_ hxb2 hs.tBar_sq hxbt
      (fun h => h0 ((hL.rho_mem_S_iff _).mpr h)) (fun h => hrtS ((hL.rho_mem_S_iff _).mpr h))
      (fun h => h1 ((hL.rho_mem_S_iff _).mpr h))
    · rw [hτb, mem_centralizer_singleton_iff]
      exact ((Commute.refl _).mul_right hxbt).eq
    · rw [hτb, mem_centralizer_singleton_iff]
      exact ((show Commute (hs.setup.tBar i j) (QuotientGroup.mk ⟨x, hxM⟩) from
        hxbt.symm).mul_right (Commute.refl _)).eq
  ·
    exact hL.false_of_graph_conj hFC hKC hI hKF hZ hτM ⟨d, hd, by rw [hτb]; exact hdg⟩

theorem false_of_conj_zt
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput)
    (hUC : GrSLit.L34UnitaryCentralizerFact) (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (hQE : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (hzM : z ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
    (m : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (hm : m * hs.setup.tBar i j * m⁻¹ = QuotientGroup.mk ⟨z, hzM⟩ * hs.setup.tBar i j) :
    False := by
  obtain ⟨x, hxD, hx2, hxM, h0, h1⟩ := hL.exists_x hZ
  have hx1 : x ≠ 1 := by
    rintro rfl
    have : (QuotientGroup.mk ⟨1, hxM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) = 1 := rfl
    exact h0 ((hL.rho_mem_S_iff _).mpr (by rw [this]; exact one_mem _))
  obtain ⟨c, hc⟩ := EndB.exists_conj_xt hKF hs hzM m hm hxD hx2 hx1
  exact hL.false_of_conj_xt hFC hKC hI hKF hUC hZ hQE hxD hx2 hxM h0 h1 hc

omit [Finite X] in
theorem conj_mem_center_map (g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    {c : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)}
    (hc : c ∈ (center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))).map
      (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype) :
    g * c * g⁻¹ ∈ (center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))).map
      (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype := by
  obtain ⟨c', hc', rfl⟩ := hc
  have hn : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := inferInstance
  have hgc := hn.conj_mem _ c'.2 g
  refine ⟨⟨_, hgc⟩, mem_center_iff.mpr fun e => Subtype.ext ?_, rfl⟩
  have he' := hn.conj_mem _ e.2 g⁻¹
  have h1 := congrArg Subtype.val (mem_center_iff.mp hc' ⟨_, he'⟩)
  simp only [Subgroup.coe_mul, inv_inv] at h1
  simp only [Subgroup.coe_mul]
  calc (e : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * (g * c' * g⁻¹) =
      g * (g⁻¹ * e * g * c') * g⁻¹ := by group
    _ = g * (c' * (g⁻¹ * e * g)) * g⁻¹ := by rw [h1]
    _ = g * c' * g⁻¹ * e := by group

theorem exists_lambda (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (h4 : Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 4) :
    ∃ l ∈ (center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))).map
        (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype,
      hs.setup.tBar i j * l * (hs.setup.tBar i j)⁻¹ =
        l * betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Zb := (center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))).map
    (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype with hZb
  set Bb := zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) with hBb
  have hβZ : betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈ Zb := hL.h412.lemma46c.2.2 hZ
  have hBZ : Bb ≤ Zb := zpowers_le.mpr hβZ
  have hβ2 := hs.betaBar_sq
  have hβ1 := hs.betaBar_ne_one
  have hBcard : Nat.card Bb = 2 := by rw [hBb, Nat.card_zpowers, orderOf_eq_prime hβ2 hβ1]
  have hZcard : Nat.card Zb = 4 := by
    rw [hZb, Subgroup.card_map_of_injective (subtype_injective _), h4]
  have hβc : ∀ y : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j),
      y * betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
        betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) * y :=
    fun y => mem_center_iff.mp (betaBar_mem_center _) y
  have hex : ∃ l ∈ Zb, l ∉ Bb := by
    by_contra h
    have hle : Zb ≤ Bb := fun l hl => by
      by_contra hl'
      exact h ⟨l, hl, hl'⟩
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨l, hlZ, hlB⟩ := hex
  have hlt : hs.setup.tBar i j * l * (hs.setup.tBar i j)⁻¹ ≠ l := by
    intro h
    apply hlB
    refine (hL.center_inf_centralizer hZ l).mp ⟨hlZ, mem_centralizer_singleton_iff.mpr ?_⟩
    calc l * hs.setup.tBar i j = hs.setup.tBar i j * l * (hs.setup.tBar i j)⁻¹ *
        hs.setup.tBar i j := by rw [h]
      _ = hs.setup.tBar i j * l := by group
  have hconj := conj_mem_center_map (hs.setup.tBar i j) hlZ
  have hcB : hs.setup.tBar i j * l * (hs.setup.tBar i j)⁻¹ ∉ Bb := by
    intro h
    apply hlB
    rcases EndB.eq_one_or_eq_of_mem_zpowers_sq hβ2 h with h1 | h1
    · have : l = 1 := by
        calc l = (hs.setup.tBar i j)⁻¹ * (hs.setup.tBar i j * l * (hs.setup.tBar i j)⁻¹) *
            hs.setup.tBar i j := by group
          _ = 1 := by rw [h1]; group
      rw [this]
      exact one_mem _
    · have : l = betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
        calc l = (hs.setup.tBar i j)⁻¹ * (hs.setup.tBar i j * l * (hs.setup.tBar i j)⁻¹) *
            hs.setup.tBar i j := by group
          _ = (hs.setup.tBar i j)⁻¹ * betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) *
            hs.setup.tBar i j := by rw [h1]
          _ = betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
            rw [mul_assoc (hs.setup.tBar i j)⁻¹ (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
              (hs.setup.tBar i j), ← hβc (hs.setup.tBar i j), inv_mul_cancel_left]
      rw [this]
      exact mem_zpowers _
  have hidx : (Bb.subgroupOf Zb).index = 2 := by
    have h1 := Subgroup.relIndex_mul_card Bb Zb
    rw [inf_of_le_left hBZ, hBcard, hZcard] at h1
    change Bb.relIndex Zb = 2
    omega
  have hmem := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨l, hlZ⟩ : ↥Zb)⁻¹)
    (b := ⟨_, hconj⟩)).mpr ⟨fun h => absurd (by
      have := inv_mem h
      rw [inv_inv, mem_subgroupOf] at this
      exact this) hlB, fun h => absurd (by rw [mem_subgroupOf] at h; exact h) hcB⟩
  rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hmem
  rcases EndB.eq_one_or_eq_of_mem_zpowers_sq hβ2 hmem with h1 | h1
  · exact absurd (by rw [inv_mul_eq_one] at h1; exact h1.symm) hlt
  · refine ⟨l, hlZ, ?_⟩
    calc hs.setup.tBar i j * l * (hs.setup.tBar i j)⁻¹ =
        l * (l⁻¹ * (hs.setup.tBar i j * l * (hs.setup.tBar i j)⁻¹)) := by group
      _ = l * betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by rw [h1]

theorem exists_conj_zt_of_E4
    (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (h4 : Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 4)
    (hQZ : (center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))).map
        (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype =
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (hnc : ¬ IsCyclic ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
    (hzM : z ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) :
    ∃ m : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j),
      m * hs.setup.tBar i j * m⁻¹ = QuotientGroup.mk ⟨z, hzM⟩ * hs.setup.tBar i j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tb := hs.setup.tBar i j with htbdef
  set zb := (QuotientGroup.mk ⟨z, hzM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) with hzbdef
  set bb := betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) with hbbdef
  have hβc : ∀ y : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j), y * bb = bb * y :=
    fun y => mem_center_iff.mp (betaBar_mem_center _) y
  have hbb2 : bb * bb = 1 := by rw [← sq]; exact hs.betaBar_sq
  have hQcard : Nat.card ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) = 4 := by
    rw [← hQZ, Subgroup.card_map_of_injective (subtype_injective _), h4]
  have hQ2 : ∀ q ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), q * q = 1 := by
    intro q hq
    have hdvd := orderOf_dvd_natCard (⟨q, hq⟩ : ↥(pCore 2 (MBar (w ^ (orderOf w / 2) *
      t ^ i * z ^ j))))
    rw [hQcard] at hdvd
    have h4' : orderOf (⟨q, hq⟩ : ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ≠ 4 :=
      fun h => hnc (isCyclic_of_orderOf_eq_card _ (by rw [h, hQcard]))
    have hle : orderOf (⟨q, hq⟩ : ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ∣ 2 := by
      have : orderOf (⟨q, hq⟩ : ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ∈
          Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have hd : Nat.divisors 4 = {1, 2, 4} := by decide
      rw [hd] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h
      · rw [h]; exact one_dvd 2
      · rw [h]
      · exact absurd h h4'
    have := orderOf_dvd_iff_pow_eq_one.mp hle
    rw [sq] at this
    exact congrArg Subtype.val this
  obtain ⟨l, hlZ, hl⟩ := hL.exists_lambda hZ h4
  have hlQ : l ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := hQZ ▸ hlZ
  have hQE : ∀ q ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      ∀ e ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), e * q = q * e := by
    intro q hq e he
    rw [← hs.centralizer_layer_eq hL.h412] at hq
    exact mem_centralizer_iff.mp hq e he
  have hzK : z ∈ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := hs.lemma45.z_mem.2
  have hzE : zb ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :=
    hs.KBar_le_layer ⟨⟨z, hzM⟩, hzK, rfl⟩
  have htM := hs.setup.t_mem_centralizer_beta i j
  have htS : t ∈ S := hs.setup.T_le (mem_sup_left (mem_sup_left (mem_zpowers t)))
  have hzt : zb * tb = tb * zb := EndB.mk_comm hzM htM (hs.setup.z_comm htS).symm
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hzb2 : zb * zb = 1 := by rw [← sq]; exact EndB.mk_sq hzM hz2
  have htb2 : tb * tb = 1 := by rw [← sq]; exact hs.tBar_sq
  have htinv : tb⁻¹ = tb := inv_eq_of_mul_eq_one_right htb2
  obtain ⟨hrt2, hrtS⟩ := hL.rho_t_facts
  set rt : Equiv.Perm (Fin 42) := ((hL.rho tb : PSL3Four.R) : Equiv.Perm (Fin 42)) with hrt
  have hrtrt : rt * rt = 1 := by
    have h := pow_orderOf_eq_one (hL.rho tb)
    rw [hrt2, sq] at h
    exact congrArg Subtype.val h
  have hrzt : ((hL.rho (zb * tb) : PSL3Four.R) : Equiv.Perm (Fin 42)) =
      (π ⟨zb, hzE⟩ : Equiv.Perm (Fin 42)) * rt := by
    rw [map_mul, Subgroup.coe_mul, ← hL.rho_of_mem ⟨zb, hzE⟩]
  have hzt2 : (zb * tb) * (zb * tb) = 1 := by
    rw [show zb * tb * (zb * tb) = zb * (tb * zb) * tb by group, ← hzt,
      show zb * (zb * tb) * tb = (zb * zb) * (tb * tb) by group, hzb2, htb2, one_mul]
  have hrzt2 : ((hL.rho (zb * tb) : PSL3Four.R) : Equiv.Perm (Fin 42)) *
      (hL.rho (zb * tb) : PSL3Four.R) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, hzt2, map_one, Subgroup.coe_one]
  have hrt1 : rt ≠ 1 := fun h => hrtS (by rw [h]; exact one_mem _)
  have hrzt1 : ((hL.rho (zb * tb) : PSL3Four.R) : Equiv.Perm (Fin 42)) ≠ 1 := by
    intro h
    apply hrtS
    have h1 : (π ⟨zb, hzE⟩ : Equiv.Perm (Fin 42)) * rt = 1 := hrzt ▸ h
    rw [eq_inv_of_mul_eq_one_right h1]
    exact inv_mem (π ⟨zb, hzE⟩).2
  have hrtR : rt ∈ PSL3Four.R := (hL.rho tb).2
  obtain ⟨y, hyS, hy⟩ := CatFactsL4U4.conj_of_mul_mem_S hrtR (hL.rho (zb * tb)).2 hrtrt hrzt2
    hrt1 hrzt1 (by
      rw [hrzt, show rt⁻¹ * ((π ⟨zb, hzE⟩ : Equiv.Perm (Fin 42)) * rt) =
        rt⁻¹ * (π ⟨zb, hzE⟩ : Equiv.Perm (Fin 42)) * rt⁻¹⁻¹ by group]
      exact PSL3Four.conj_mem_S (inv_mem hrtR) (π ⟨zb, hzE⟩).2)
  obtain ⟨e, he⟩ := hL.surj ⟨y, hyS⟩
  have hρe : ((hL.rho (e : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) : PSL3Four.R) :
      Equiv.Perm (Fin 42)) = y := by rw [hL.rho_of_mem e, he]
  set eb : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) :=
    (e : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) with hebdef
  have hconj : hL.rho (eb * tb * eb⁻¹) = hL.rho (zb * tb) := by
    apply Subtype.ext
    rw [show hL.rho (eb * tb * eb⁻¹) = hL.rho eb * hL.rho tb * (hL.rho eb)⁻¹ by
      rw [map_mul, map_mul, map_inv], Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hρe]
    exact hy
  set d := (eb * tb * eb⁻¹) * (zb * tb)⁻¹ with hddef
  have hdQ : d ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    rw [← hL.rho_eq_one_iff, hddef, MonoidHom.map_mul hL.rho (eb * tb * eb⁻¹) (zb * tb)⁻¹,
      map_inv, hconj, mul_inv_cancel]
  have hetb : eb * tb * eb⁻¹ = d * (zb * tb) := by rw [hddef]; group
  have hQn : (pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := pCore_normal
  set d' := tb * d * tb⁻¹ with hd'def
  have hd'Q : d' ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :=
    hQn.conj_mem d hdQ tb
  have hzd' : zb * d' = d' * zb := hQE d' hd'Q zb hzE
  have h1 : (d * (zb * tb)) * (d * (zb * tb)) = 1 := by
    rw [← hetb, show eb * tb * eb⁻¹ * (eb * tb * eb⁻¹) = eb * (tb * tb) * eb⁻¹ by group, htb2]
    group
  have hdd' : d * d' = 1 := by
    calc d * d' = d * d' * (zb * zb) := by rw [hzb2, mul_one]
      _ = d * (zb * d') * zb := by rw [hzd']; group
      _ = d * zb * tb * d * (tb⁻¹ * zb) := by rw [hd'def]; group
      _ = d * zb * tb * d * (zb * tb) := by rw [htinv, ← hzt]
      _ = (d * (zb * tb)) * (d * (zb * tb)) := by group
      _ = 1 := h1
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right (hQ2 d hdQ)
  have hdt : d ∈ centralizer {tb} := by
    rw [mem_centralizer_singleton_iff]
    have : d' = d := by rw [eq_inv_of_mul_eq_one_right hdd', hdinv]
    calc d * tb = tb * (tb⁻¹ * d * tb) := by group
      _ = tb * d' := by rw [hd'def, htinv]
      _ = tb * d := by rw [this]
  have hdB : d ∈ zpowers bb := by
    rw [hbbdef, ← hL.h412.pCore_inf_centralizer]
    exact mem_inf.mpr ⟨hdQ, hdt⟩
  rcases EndB.eq_one_or_eq_of_mem_zpowers_sq hs.betaBar_sq hdB with hd1 | hd1
  · refine ⟨eb, ?_⟩
    rw [hetb, hd1, one_mul]
  · refine ⟨l⁻¹ * eb, ?_⟩
    have hlt : l⁻¹ * tb * l = bb * tb := by
      calc l⁻¹ * tb * l = l⁻¹ * (tb * l * tb⁻¹) * tb := by group
        _ = l⁻¹ * (l * bb) * tb := by rw [hl]
        _ = bb * tb := by group
    have hlz : zb * l = l * zb := hQE l hlQ zb hzE
    calc l⁻¹ * eb * tb * (l⁻¹ * eb)⁻¹ = l⁻¹ * (eb * tb * eb⁻¹) * l := by group
      _ = l⁻¹ * (bb * (zb * tb)) * l := by rw [hetb, hd1]
      _ = bb * l⁻¹ * (zb * tb) * l := by rw [← hβc l⁻¹]; group
      _ = bb * zb * (l⁻¹ * tb * l) := by
        rw [show bb * l⁻¹ * (zb * tb) * l = bb * (l⁻¹ * zb) * tb * l by group,
          show l⁻¹ * zb = zb * l⁻¹ by
            calc l⁻¹ * zb = l⁻¹ * (zb * l) * l⁻¹ := by group
              _ = l⁻¹ * (l * zb) * l⁻¹ := by rw [hlz]
              _ = zb * l⁻¹ := by group]
        group
      _ = bb * zb * (bb * tb) := by rw [hlt]
      _ = zb * tb := by
        rw [show bb * zb * (bb * tb) = bb * (zb * bb) * tb by group, hβc zb,
          show bb * (bb * zb) * tb = (bb * bb) * zb * tb by group, hbb2, one_mul]

theorem false_of_E4
    (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput)
    (hUC : GrSLit.L34UnitaryCentralizerFact) (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (h4 : Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 4)
    (hQZ : (center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))).map
        (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).subtype =
      pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (hnc : ¬ IsCyclic ↥(pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) : False := by
  have hzM : z ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
    K_le_centralizer_beta i j hs.lemma45.z_mem.2
  obtain ⟨m, hm⟩ := hL.exists_conj_zt_of_E4 hZ h4 hQZ hnc hzM
  exact hL.false_of_conj_zt hFC hKC hI hKF hUC hZ (hQZ ▸ map_subtype_le _) hzM m hm

end EndB.LLayer

end CFSG.ComponentClassification.HarrisLit
