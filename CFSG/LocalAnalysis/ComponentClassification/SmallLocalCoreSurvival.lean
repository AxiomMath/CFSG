module

public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalThompson

public section

namespace CFSG.ComponentClassification.SmallLocal

open Subgroup

variable {G : Type*} [Group G]

theorem inv_mul_mul_eq_iff {x y : G} : y⁻¹ * x * y = x ↔ x * y = y * x := by
  constructor
  · intro h
    calc x * y = y * (y⁻¹ * x * y) := by group
      _ = y * x := by rw [h]
  · intro h
    rw [mul_assoc, h, inv_mul_cancel_left]

theorem le_normalizer_of_conj_mem {X M : Subgroup G} (h : ∀ g ∈ X, ∀ m ∈ M, g * m * g⁻¹ ∈ M) :
    X ≤ normalizer (M : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro m
  refine ⟨h g hg m, fun hm => ?_⟩
  have h1 := h g⁻¹ (inv_mem hg) _ hm
  have h2 : g⁻¹ * (g * m * g⁻¹) * g⁻¹⁻¹ = m := by group
  rwa [h2] at h1

theorem conj_mem_sup {A B M : Subgroup G} {g : G} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ M)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ M) : ∀ x ∈ A ⊔ B, g * x * g⁻¹ ∈ M := by
  have hle : (A ⊔ B).map (MulAut.conj g).toMonoidHom ≤ M := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact hA a ha
    · rintro _ ⟨b, hb, rfl⟩
      exact hB b hb
  exact fun x hx => hle ⟨x, hx, rfl⟩

theorem conj_mem_pPrimeCore_map {M : Subgroup G} (p : ℕ) {g : G}
    (hg : g ∈ normalizer (M : Set G)) {x : G} (hx : x ∈ (pPrimeCore p M).map M.subtype) :
    g * x * g⁻¹ ∈ (pPrimeCore p M).map M.subtype := by
  obtain ⟨m, hm, rfl⟩ := hx
  have hfix := (inferInstance : (pPrimeCore p M).Characteristic).fixed
    (M.normalizerMonoidHom ⟨g, hg⟩)
  have hφm : M.normalizerMonoidHom ⟨g, hg⟩ m ∈ pPrimeCore p M :=
    (Subgroup.ext_iff.mp hfix m).mpr hm
  exact ⟨_, hφm, normalizerMonoidHom_apply_apply_coe M ⟨g, hg⟩ m⟩

theorem odd_centralizer_core_survives_centralized_prime_core {K : Type*} [Group K] [Finite K]
    {p : ℕ} (hp : p.Prime) {Q P D : Subgroup K} [hQn : Q.Normal] (hQ : Q ≠ ⊥) [hPn : P.Normal]
    (hPp : IsPGroup p P) (hPQ : ⁅P, Q⁆ = ⊥) {y : K} (hy : orderOf y = p)
    (hDC : D ≤ centralizer ({y} : Set K))
    (hDn : (D.subgroupOf (centralizer ({y} : Set K))).Normal)
    (hDp : Nat.Coprime p (Nat.card D)) (hK : Q ⊔ D ⊔ zpowers y = ⊤)
    (hQy : ⁅Q, zpowers y⁆ = Q) (hQD : ⁅Q, D⁆ = Q) :
    orderOf (QuotientGroup.mk' P y) = p ∧ D.map (QuotientGroup.mk' P) ≠ ⊥ ∧
      D.map (QuotientGroup.mk' P) ≤
        (pPrimeCore p (centralizer ({QuotientGroup.mk' P y} : Set (K ⧸ P)))).map
          (centralizer ({QuotientGroup.mk' P y} : Set (K ⧸ P))).subtype ∧
      ⁅P, D⁆ = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  set Cy := centralizer ({y} : Set K) with hCy
  have hmemCy : ∀ x : K, x ∈ Cy ↔ x * y = y * x := fun x => mem_centralizer_singleton_iff
  have hdisj : Disjoint D P := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hPp
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact (hDp.pow_left n).symm
  have hyp : IsPGroup p (zpowers y) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hy, pow_one])
  have hDP : ∀ d ∈ D, ∀ x ∈ P, d * x = x * d := by
    refine thompson_subgroup hPp hDp hyp ?_ ?_
    · intro d hd b hb
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
      exact Commute.zpow_right ((hmemCy d).mp (hDC hd)) k
    · intro d hd x hx hxy
      have hxC : x ∈ Cy := (hmemCy x).mpr (hxy y (mem_zpowers y)).symm
      have h1 : x * d⁻¹ * x⁻¹ ∈ D := mem_subgroupOf.mp
        (hDn.conj_mem ⟨d⁻¹, hDC (inv_mem hd)⟩ (mem_subgroupOf.mpr (inv_mem hd)) ⟨x, hxC⟩)
      have hcD : d * x * d⁻¹ * x⁻¹ ∈ D := by
        have h2 := mul_mem hd h1
        simpa only [mul_assoc] using h2
      have hcP : d * x * d⁻¹ * x⁻¹ ∈ P := mul_mem (hPn.conj_mem x hx d) (inv_mem hx)
      have hc1 := disjoint_def.mp hdisj hcD hcP
      calc d * x = d * x * d⁻¹ * x⁻¹ * (x * d) := by group
        _ = x * d := by rw [hc1, one_mul]
  have hPD : ⁅P, D⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    exact fun d hd => hDP d hd x hx
  have hyP : y ∉ P := by
    intro hyP
    apply hQ
    have h1 : ⁅Q, zpowers y⁆ ≤ ⁅Q, P⁆ := commutator_mono le_rfl (zpowers_le.mpr hyP)
    rw [commutator_comm Q P, hPQ, hQy] at h1
    exact le_bot_iff.mp h1
  have hπy : orderOf (QuotientGroup.mk' P y) = p := by
    have hdvd : orderOf (QuotientGroup.mk' P y) ∣ p := hy ▸ orderOf_map_dvd _ y
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exfalso
      rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      exact hyP h
    · exact h
  have hπD : D.map (QuotientGroup.mk' P) ≠ ⊥ := by
    intro h
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    apply hQ
    rw [← hQD, hdisj.eq_bot_of_le h, commutator_bot_right]
  set Cbar := centralizer ({QuotientGroup.mk' P y} : Set (K ⧸ P)) with hCbar
  set C := Cbar.comap (QuotientGroup.mk' P) with hC
  have hmemC : ∀ x : K, x ∈ C ↔ QuotientGroup.mk' P x * QuotientGroup.mk' P y =
      QuotientGroup.mk' P y * QuotientGroup.mk' P x :=
    fun x => by rw [hC, mem_comap, hCbar, mem_centralizer_singleton_iff]
  have hCyC : Cy ≤ C := fun x hx => by
    rw [hmemC, ← map_mul, ← map_mul, (hmemCy x).mp hx]
  set N := Q ⊓ Cy with hN
  set M := N ⊔ D with hM
  have hMCy : M ≤ Cy := sup_le inf_le_right hDC
  have hMC : M ≤ C := hMCy.trans hCyC
  have hDM : D ≤ M := le_sup_right
  have hCle : C ≤ (Q ⊓ C) ⊔ (D ⊔ zpowers y) := by
    intro c hc
    have hctop : c ∈ Q ⊔ (D ⊔ zpowers y) := by
      rw [← sup_assoc, hK]
      exact mem_top c
    rw [← SetLike.mem_coe, normal_mul, Set.mem_mul] at hctop
    obtain ⟨q, hq, x, hx, rfl⟩ := hctop
    have hxC : x ∈ C := hCyC (sup_le hDC (zpowers_le.mpr ((hmemCy y).mpr rfl)) hx)
    have hqC : q ∈ C := by
      have h1 := mul_mem hc (inv_mem hxC)
      rwa [mul_inv_cancel_right] at h1
    exact mul_mem_sup (mem_inf.mpr ⟨hq, hqC⟩) hx
  have hyN : zpowers y ≤ normalizer (M : Set K) := by
    refine (zpowers_le.mpr ?_).trans (centralizer_le_normalizer _)
    rw [mem_centralizer_iff]
    exact fun m hm => (hmemCy m).mp (hMCy hm)
  have hDN : D ≤ normalizer (M : Set K) := by
    refine le_normalizer_of_conj_mem fun d hd => conj_mem_sup ?_ ?_
    · intro n hn
      obtain ⟨hnQ, hnCy⟩ := mem_inf.mp hn
      have hd' : Commute d y := (hmemCy d).mp (hDC hd)
      have hn' : Commute n y := (hmemCy n).mp hnCy
      exact mem_sup_left (mem_inf.mpr ⟨hQn.conj_mem n hnQ d,
        (hmemCy _).mpr ((hd'.mul_left hn').mul_left hd'.inv_left)⟩)
    · intro b hb
      exact mem_sup_right (mul_mem (mul_mem hd hb) (inv_mem hd))
  have hQCN : Q ⊓ C ≤ normalizer (M : Set K) := by
    refine le_normalizer_of_conj_mem fun q hq => ?_
    obtain ⟨hqQ, hqC⟩ := mem_inf.mp hq
    obtain ⟨z, hz⟩ : ∃ z, z = q⁻¹ * y⁻¹ * q * y := ⟨_, rfl⟩
    have hzP : z ∈ P := by
      have hcomm := (hmemC q).mp hqC
      have h1 : QuotientGroup.mk' P z = 1 := by
        rw [hz, map_mul, map_mul, map_mul, map_inv, map_inv,
          mul_assoc _ (QuotientGroup.mk' P q), hcomm]
        group
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hyq : y⁻¹ * q * y = q * z := by
      rw [hz]
      group
    have hzQ : ∀ n ∈ Q, z * n = n * z := fun n hn =>
      ((mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hPQ hzP)) n hn).symm
    refine conj_mem_sup ?_ ?_
    · intro n hn
      obtain ⟨hnQ, hnCy⟩ := mem_inf.mp hn
      have hyn : y⁻¹ * n * y = n := inv_mul_mul_eq_iff.mpr ((hmemCy n).mp hnCy)
      refine mem_sup_left (mem_inf.mpr ⟨hQn.conj_mem n hnQ q, (hmemCy _).mpr
        (inv_mul_mul_eq_iff.mp ?_)⟩)
      calc y⁻¹ * (q * n * q⁻¹) * y = (y⁻¹ * q * y) * (y⁻¹ * n * y) * (y⁻¹ * q * y)⁻¹ := by
            group
        _ = q * (z * n) * z⁻¹ * q⁻¹ := by
            rw [hyq, hyn]
            group
        _ = q * n * q⁻¹ := by
            rw [hzQ n hnQ]
            group
    · intro d hd
      have hyd : y⁻¹ * d * y = d := inv_mul_mul_eq_iff.mpr ((hmemCy d).mp (hDC hd))
      have hcQ : q * d * q⁻¹ * d⁻¹ ∈ Q := by
        have h1 : q * d * q⁻¹ * d⁻¹ = q * (d * q⁻¹ * d⁻¹) := by group
        rw [h1]
        exact mul_mem hqQ (hQn.conj_mem q⁻¹ (inv_mem hqQ) d)
      have hcy : y⁻¹ * (q * d * q⁻¹ * d⁻¹) * y = q * d * q⁻¹ * d⁻¹ := by
        calc y⁻¹ * (q * d * q⁻¹ * d⁻¹) * y =
            (y⁻¹ * q * y) * (y⁻¹ * d * y) * (y⁻¹ * q * y)⁻¹ * (y⁻¹ * d * y)⁻¹ := by group
          _ = q * (z * d) * z⁻¹ * q⁻¹ * d⁻¹ := by
            rw [hyq, hyd]
            group
          _ = q * d * q⁻¹ * d⁻¹ := by
            rw [(hDP d hd z hzP).symm]
            group
      have hcN : q * d * q⁻¹ * d⁻¹ ∈ N :=
        mem_inf.mpr ⟨hcQ, (hmemCy _).mpr (inv_mul_mul_eq_iff.mp hcy)⟩
      have h1 : q * d * q⁻¹ = q * d * q⁻¹ * d⁻¹ * d := by group
      rw [h1]
      exact mul_mem_sup hcN hd
  have hCN : C ≤ normalizer (M : Set K) := hCle.trans (sup_le hQCN (sup_le hDN hyN))
  have hDMn : (D.subgroupOf M).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    exact mem_subgroupOf.mp
      (hDn.conj_mem ⟨n, hDC hn⟩ (mem_subgroupOf.mpr hn) ⟨g, hMCy g.2⟩)
  set L := (pPrimeCore p M).map M.subtype with hL
  have hDL : D ≤ L := by
    have hle : D.subgroupOf M ≤ pPrimeCore p M := by
      refine le_sSup (s := {X : Subgroup M | X.Normal ∧ Nat.Coprime p (Nat.card X)}) ⟨hDMn, ?_⟩
      rwa [Nat.card_congr (subgroupOfEquivOfLe hDM).toEquiv]
    have h1 := map_mono (f := M.subtype) hle
    rwa [subgroupOf_map_subtype, inf_eq_left.mpr hDM] at h1
  have hLC : ∀ c ∈ C, ∀ l ∈ L, c * l * c⁻¹ ∈ L := fun c hc l hl =>
    conj_mem_pPrimeCore_map p (hCN hc) hl
  have hLCbar : L.map (QuotientGroup.mk' P) ≤ Cbar := by
    rintro _ ⟨l, hl, rfl⟩
    exact hMC (map_subtype_le _ hl)
  have hcore : (L.map (QuotientGroup.mk' P)).subgroupOf Cbar ≤ pPrimeCore p Cbar := by
    refine le_sSup (s := {X : Subgroup Cbar | X.Normal ∧ Nat.Coprime p (Nat.card X)})
      ⟨⟨fun w hw u => ?_⟩, ?_⟩
    · rw [mem_subgroupOf] at hw ⊢
      obtain ⟨l, hl, hlw⟩ := hw
      obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective P (u : K ⧸ P)
      have hcC : c ∈ C := by
        rw [hC, mem_comap, hc]
        exact u.2
      refine ⟨c * l * c⁻¹, hLC c hcC l hl, ?_⟩
      rw [map_mul, map_mul, map_inv, hc, hlw]
      rfl
    · have h1 : Nat.card ((L.map (QuotientGroup.mk' P)).subgroupOf Cbar) =
          Nat.card (L.map (QuotientGroup.mk' P)) :=
        Nat.card_congr (subgroupOfEquivOfLe hLCbar).toEquiv
      have h2 : Nat.card L = Nat.card (pPrimeCore p M) := card_map_of_injective M.subtype_injective
      rw [h1]
      refine (pPrimeCore_coprime_card (G := M)).coprime_dvd_right ?_
      rw [← h2]
      exact card_map_dvd L _
  refine ⟨hπy, hπD, ?_, hPD⟩
  calc D.map (QuotientGroup.mk' P) ≤ L.map (QuotientGroup.mk' P) := map_mono hDL
    _ = ((L.map (QuotientGroup.mk' P)).subgroupOf Cbar).map Cbar.subtype := by
        rw [subgroupOf_map_subtype, inf_eq_left.mpr hLCbar]
    _ ≤ (pPrimeCore p Cbar).map Cbar.subtype := map_mono hcore

end CFSG.ComponentClassification.SmallLocal
