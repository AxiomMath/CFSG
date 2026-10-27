module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19MinSwap
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Assembly
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19MinBasic

public section

namespace CFSG.QuasithinUnique.Id2519.HS4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Swap

variable {G : Type} [Group G]

theorem exists_fixed_involution_or_inf_eq_bot [Finite G] {R0 D : Subgroup G} {s : G}
    (hW : IsPGroup 2 ↥(D ⊔ Subgroup.zpowers s)) (hR0D : R0 ≤ D)
    (hR0n : D ≤ Subgroup.normalizer (R0 : Set G))
    (hsD : s ∈ Subgroup.normalizer (D : Set G)) (hs2 : s ^ 2 ∈ D) :
    R0 ⊓ CFSG.conjugate R0 s = ⊥ ∨ ∃ r ∈ R0 ⊓ CFSG.conjugate R0 s, r ≠ 1 ∧ r ^ 2 = 1 ∧
      ∀ w ∈ D ⊔ Subgroup.zpowers s, w * r = r * w := by
  classical
  set Q : Subgroup G := R0 ⊓ CFSG.conjugate R0 s with hQ
  have hDQ : D ≤ Subgroup.normalizer (Q : Set G) := by
    intro d hd
    refine mem_normalizer_inf' (hR0n hd) (mem_normalizer_conjugate_of ?_)
    have hd' : s * d * s⁻¹ ∈ D := by
      have := Subgroup.mem_normalizer_iff.mp hsD d
      exact this.mp hd
    exact hR0n hd'
  have hss : s * s ∈ Subgroup.normalizer (R0 : Set G) := by
    rw [← pow_two]; exact hR0n hs2
  have hsQ : s ∈ Subgroup.normalizer (Q : Set G) := by
    rw [← BenderBranch.conjugate_eq_iff_mem_normalizer]
    have e2 : CFSG.conjugate R0 (s * s) = R0 :=
      BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hss
    rw [hQ, BenderBranch.conjugate_inf, BenderBranch.conjugate_conjugate, e2, inf_comm]
  have hWQ : D ⊔ Subgroup.zpowers s ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le hDQ ((Subgroup.zpowers_le).mpr hsQ)
  by_cases hQ1 : Q = ⊥
  · exact Or.inl hQ1
  · right
    have hQW : Q ≤ D ⊔ Subgroup.zpowers s :=
      (inf_le_left.trans hR0D).trans le_sup_left
    have hne := inf_centralizer_ne_bot_of_normalizes hW hQW hWQ hQ1
    have hP2 : IsPGroup 2 ↥(Q ⊓ Subgroup.centralizer ((D ⊔ Subgroup.zpowers s : Subgroup G) :
        Set G)) := hW.to_le (inf_le_left.trans hQW)
    obtain ⟨r, hr, hr1, hr2⟩ := exists_involution_of_isPGroup_ne_bot hP2 hne
    have hrQ : r ∈ Q := hr.1
    exact ⟨r, hrQ, hr1, hr2, fun w hw => Subgroup.mem_centralizer_iff.mp hr.2 w hw⟩

end Swap

section SemiD

theorem semidihedral_four_sq_ne_one :
    (PresentedGroup.of 0 : SemidihedralGroup 4) * PresentedGroup.of 0 ≠ 1 := by
  let c : Equiv.Perm (Fin 8) := List.formPerm [0, 1, 2, 3, 4, 5, 6, 7]
  let m : Equiv.Perm (Fin 8) := List.formPerm [1, 3] * List.formPerm [2, 6] * List.formPerm [5, 7]
  let f : Fin 2 → Equiv.Perm (Fin 8) := fun j => if j = 0 then c else m
  have hrel : ∀ r ∈ semidihedralRels 4, FreeGroup.lift f r = 1 := by
    intro r hr
    simp only [semidihedralRels, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl
    · simp only [map_pow, FreeGroup.lift_apply_of, f]
      decide +kernel
    · simp only [map_pow, FreeGroup.lift_apply_of, f]
      decide +kernel
    · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, f]
      decide +kernel
  let φ : SemidihedralGroup 4 →* Equiv.Perm (Fin 8) := PresentedGroup.toGroup hrel
  intro h1
  have h2 : φ (PresentedGroup.of 0 * PresentedGroup.of 0) = 1 := by rw [h1, map_one]
  rw [map_mul, PresentedGroup.toGroup.of] at h2
  revert h2
  simp only [f]
  decide +kernel

end SemiD

section SK

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G}

theorem exists_sq_ne_one_SK (h : Lv2518 N t zK) : ∃ a ∈ N.SK, a * a ≠ 1 := by
  rcases h.facts258.SK_shape with ⟨n, hn4, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · refine ⟨((e.symm (DihedralGroup.r 1) : ↥N.SK) : G), (e.symm (DihedralGroup.r 1)).2, ?_⟩
    intro h1
    have h2 : e.symm (DihedralGroup.r 1) * e.symm (DihedralGroup.r 1) = 1 :=
      Subtype.ext (by simpa using h1)
    rw [← map_mul, ← map_one e.symm] at h2
    have h3 := e.symm.injective h2
    simp only [DihedralGroup.r_mul_r, DihedralGroup.one_def, DihedralGroup.r.injEq] at h3
    have h4 : (2 : ZMod n) = 0 := by simpa [one_add_one_eq_two] using h3
    have h5 : n ∣ 2 := by
      have := (ZMod.natCast_eq_zero_iff 2 n).mp (by exact_mod_cast h4)
      exact this
    have := Nat.le_of_dvd (by norm_num) h5
    omega
  · refine ⟨((e.symm (PresentedGroup.of 0) : ↥N.SK) : G), (e.symm (PresentedGroup.of 0)).2, ?_⟩
    intro h1
    have h2 : e.symm (PresentedGroup.of 0) * e.symm (PresentedGroup.of 0) = 1 :=
      Subtype.ext (by simpa using h1)
    rw [← map_mul, ← map_one e.symm] at h2
    exact semidihedral_four_sq_ne_one (e.symm.injective h2)

end SK

section Extremal

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK i : G}

omit [Finite G] in
theorem mem_normalizer_centralizer_of' {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) := by
  rw [← BenderBranch.conjugate_eq_iff_mem_normalizer, BenderBranch.conjugate_centralizer,
    BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hg]

theorem exponent_two_of_extremal
    (M2 : ∀ j : G, Hyp2519 N j → Nat.card (Rgrp2519 N j) = Nat.card (Rgrp2519 N i) →
      Nat.card ↥(N.S ⊓ Subgroup.centralizer ({j} : Set G)) ≤
        Nat.card ↥(N.S ⊓ Subgroup.centralizer ({i} : Set G)))
    (hB : N.S ⊓ Subgroup.centralizer (N.K : Set G) ≤ N.S ⊓ Subgroup.centralizer ({i} : Set G))
    (hCiK : ∀ c ∈ N.S ⊓ Subgroup.centralizer ({i} : Set G), c ∈ Subgroup.normalizer (N.K : Set G))
    (hn : ∃ n ∈ N.S ⊓ Subgroup.normalizer (N.K : Set G), n * i ≠ i * n)
    {R0 : Subgroup G} (hR0R : R0 ≤ Rgrp2519 N i)
    (hR0norm : ∀ c ∈ N.S ⊓ Subgroup.centralizer ({i} : Set G),
      c ∈ Subgroup.normalizer (N.K : Set G) → c ∈ Subgroup.normalizer (R0 : Set G))
    (hR0nc : ∀ r ∈ R0, r ≠ 1 → r ^ 2 = 1 →
      ¬ IsComponentIn N.K (Subgroup.centralizer ({r} : Set G)))
    (hR0exp : ∀ r ∈ Rgrp2519 N i, r * r ∈ R0) :
    ∀ r ∈ Rgrp2519 N i, r * r = 1 := by
  obtain ⟨n, ⟨hnS, hnK⟩, hn⟩ := hn
  have hS2 : IsPGroup 2 N.S := N.tuple.sylow.isPGroup
  have hRCs : Rgrp2519 N i = N.S ⊓ Subgroup.centralizer (N.K : Set G) := inf_eq_right.mpr hB
  have hCiNK : N.S ⊓ Subgroup.centralizer ({i} : Set G) <
      N.S ⊓ Subgroup.normalizer (N.K : Set G) := by
    refine lt_of_le_of_ne (fun c hc => ⟨hc.1, hCiK c hc⟩) fun e => ?_
    have hmem : n ∈ N.S ⊓ Subgroup.normalizer (N.K : Set G) := ⟨hnS, hnK⟩
    rw [← e] at hmem
    exact hn (Subgroup.mem_centralizer_singleton_iff.mp hmem.2)
  have hNK2 : IsPGroup 2 ↥(N.S ⊓ Subgroup.normalizer (N.K : Set G)) := hS2.to_le inf_le_left
  obtain ⟨s, hsNK, hsCi, hs2⟩ := exists_mem_normalizer_not_mem_sq_mem hNK2 hCiNK
  have hsS : s ∈ N.S := hsNK.1.1
  have hsK : s ∈ Subgroup.normalizer (N.K : Set G) := hsNK.1.2
  have hsD : s ∈ Subgroup.normalizer ((N.S ⊓ Subgroup.centralizer ({i} : Set G) : Subgroup G) :
      Set G) := hsNK.2
  have hWS : N.S ⊓ Subgroup.centralizer ({i} : Set G) ⊔ Subgroup.zpowers s ≤ N.S :=
    sup_le inf_le_left ((Subgroup.zpowers_le).mpr hsS)
  have hW : IsPGroup 2 ↥(N.S ⊓ Subgroup.centralizer ({i} : Set G) ⊔ Subgroup.zpowers s) :=
    hS2.to_le hWS
  have hRD : Rgrp2519 N i ≤ N.S ⊓ Subgroup.centralizer ({i} : Set G) := by
    rw [hRCs]; exact hB
  have hR0D : R0 ≤ N.S ⊓ Subgroup.centralizer ({i} : Set G) := hR0R.trans hRD
  have hR0n : N.S ⊓ Subgroup.centralizer ({i} : Set G) ≤ Subgroup.normalizer (R0 : Set G) :=
    fun c hc => hR0norm c hc (hCiK c hc)
  have hsR : s ∈ Subgroup.normalizer (Rgrp2519 N i : Set G) := by
    rw [hRCs]
    exact mem_normalizer_inf' (Subgroup.le_normalizer hsS) (mem_normalizer_centralizer_of' hsK)
  rcases exists_fixed_involution_or_inf_eq_bot hW hR0D hR0n hsD hs2 with hbot | ⟨r, hrQ, hr1, hr2, hc⟩
  · intro r hr
    have h1 : r * r ∈ R0 := hR0exp r hr
    have h2 : r * r ∈ CFSG.conjugate R0 s := by
      rw [BenderBranch.mem_conjugate_iff]
      have hr' : s * r * s⁻¹ ∈ Rgrp2519 N i :=
        (Subgroup.mem_normalizer_iff.mp hsR r).mp hr
      have e : s * (r * r) * s⁻¹ = (s * r * s⁻¹) * (s * r * s⁻¹) := by group
      rw [e]
      exact hR0exp _ hr'
    have h3 : r * r ∈ R0 ⊓ CFSG.conjugate R0 s := ⟨h1, h2⟩
    rw [hbot, Subgroup.mem_bot] at h3
    exact h3
  · exfalso
    have hrR0 : r ∈ R0 := hrQ.1
    have hHr : Hyp2519 N r := ⟨(hR0R hrR0).2, hr1, hr2, hR0nc r hrR0 hr1 hr2⟩
    have hWr : N.S ⊓ Subgroup.centralizer ({i} : Set G) ⊔ Subgroup.zpowers s ≤
        N.S ⊓ Subgroup.centralizer ({r} : Set G) :=
      fun w hw => ⟨hWS hw, Subgroup.mem_centralizer_singleton_iff.mpr (hc w hw)⟩
    have hCsr : N.S ⊓ Subgroup.centralizer (N.K : Set G) ≤
        N.S ⊓ Subgroup.centralizer ({r} : Set G) :=
      fun w hw => hWr (Subgroup.mem_sup_left (hB hw))
    have hRr : Rgrp2519 N r = N.S ⊓ Subgroup.centralizer (N.K : Set G) :=
      inf_eq_right.mpr hCsr
    have hcard : Nat.card (Rgrp2519 N r) = Nat.card (Rgrp2519 N i) := by rw [hRr, hRCs]
    have h2 := M2 r hHr hcard
    have hlt : N.S ⊓ Subgroup.centralizer ({i} : Set G) <
        N.S ⊓ Subgroup.centralizer ({i} : Set G) ⊔ Subgroup.zpowers s := by
      refine lt_of_le_of_ne le_sup_left fun e => hsCi ?_
      rw [e]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
    have h3 := Subgroup.card_lt_of_lt hlt
    have h4 := Subgroup.card_le_of_le hWr
    omega

theorem K0_eq_K (h : Lv2518 N t zK)
    (hexp : ∀ r ∈ N.S ⊓ Subgroup.centralizer (N.K : Set G), r * r = 1) : N.K0 = N.K := by
  rcases h.facts254.shape with h0 | ⟨g, hgS, hne, hK0, hcom⟩
  · exact h0
  · exfalso
    obtain ⟨a, haSK, ha⟩ := exists_sq_ne_one_SK h
    have haS : a ∈ N.S := haSK.1
    have haK : a ∈ N.K := haSK.2
    have hmem : g⁻¹ * a * g ∈ N.S ⊓ Subgroup.centralizer (N.K : Set G) := by
      refine ⟨N.S.mul_mem (N.S.mul_mem (N.S.inv_mem hgS) haS) hgS, ?_⟩
      show g⁻¹ * a * g ∈ Subgroup.centralizer (N.K : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hKle : N.K ≤ Subgroup.centralizer (CFSG.conjugate N.K g : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcom
      have hy : g⁻¹ * a * g ∈ CFSG.conjugate N.K g := by
        rw [BenderBranch.mem_conjugate_iff]
        have e : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
        rw [e]
        exact haK
      exact (Subgroup.mem_centralizer_iff.mp (hKle hk) _ hy).symm
    have h2 := hexp _ hmem
    apply ha
    have e : a * a = g * ((g⁻¹ * a * g) * (g⁻¹ * a * g)) * g⁻¹ := by group
    rw [e, h2]
    group

theorem card_centerOf_inf_SC_le_two (h : Lv2518 N t zK) :
    Nat.card ↥(centerOf N.S ⊓ N.SC) ≤ 2 := by
  have hf := h.facts2511
  have h4 : Nat.card ↥(centerOf N.S) = 4 := hf.centerS_E4.2
  have hzKc : zK ∈ centerOf N.S := by
    rw [hf.centerS_zK]
    exact Subgroup.subset_closure (Or.inr rfl)
  have hlt : centerOf N.S ⊓ N.SC < centerOf N.S := by
    refine lt_of_le_of_ne inf_le_left fun e => ?_
    have hle : centerOf N.S ≤ N.SC := inf_eq_left.mp e
    have hz1 : zK ∈ N.K0 ⊓ N.SC := ⟨hf.zK_mem, hle hzKc⟩
    rw [h.facts258.K0_inf_SC, Subgroup.mem_bot] at hz1
    have hcl : centerOf N.S ≤ Subgroup.zpowers t := by
      rw [hf.centerS_zK, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_zpowers _
      · rw [hz1]; exact Subgroup.one_mem _
    have h2 : Nat.card ↥(Subgroup.zpowers t) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) hf.t_sq
    have := Subgroup.card_le_of_le hcl
    omega
  have h1 := Subgroup.card_lt_of_lt hlt
  have h3 : Nat.card ↥(centerOf N.S ⊓ N.SC) ∣ 4 := h4 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hle4 : Nat.card ↥(centerOf N.S ⊓ N.SC) ≤ 4 := Nat.le_of_dvd (by norm_num) h3
  have hne3 : Nat.card ↥(centerOf N.S ⊓ N.SC) ≠ 3 := by
    intro e3
    rw [e3] at h3
    exact absurd h3 (by norm_num)
  omega

theorem hs4_false_of_fin (h : Lv2518 N t zK)
    (hfin : ∀ P E : Subgroup (MulAut ↥N.K), IsPGroup 2 ↥P →
      (∀ g ∈ P, ∀ e ∈ E, g * e * g⁻¹ ∈ E) → (∀ e ∈ E, e * e = 1) → 8 ≤ Nat.card ↥E →
      4 ≤ Nat.card ↥(E ⊓ Subgroup.centralizer (P : Set (MulAut ↥N.K))))
    (M2 : ∀ j : G, Hyp2519 N j → Nat.card (Rgrp2519 N j) = Nat.card (Rgrp2519 N i) →
      Nat.card ↥(N.S ⊓ Subgroup.centralizer ({j} : Set G)) ≤
        Nat.card ↥(N.S ⊓ Subgroup.centralizer ({i} : Set G)))
    (hB : N.S ⊓ Subgroup.centralizer (N.K : Set G) ≤ N.S ⊓ Subgroup.centralizer ({i} : Set G))
    (hCiK : ∀ c ∈ N.S ⊓ Subgroup.centralizer ({i} : Set G), c ∈ Subgroup.normalizer (N.K : Set G))
    (hn : ∃ n ∈ N.S ⊓ Subgroup.normalizer (N.K : Set G), n * i ≠ i * n)
    {R0 : Subgroup G} (hR0R : R0 ≤ Rgrp2519 N i)
    (hR0norm : ∀ c ∈ N.S ⊓ Subgroup.centralizer ({i} : Set G),
      c ∈ Subgroup.normalizer (N.K : Set G) → c ∈ Subgroup.normalizer (R0 : Set G))
    (hR0nc : ∀ r ∈ R0, r ≠ 1 → r ^ 2 = 1 →
      ¬ IsComponentIn N.K (Subgroup.centralizer ({r} : Set G)))
    (hR0exp : ∀ r ∈ Rgrp2519 N i, r * r ∈ R0)
    (hbig : 4 < Nat.card (Rgrp2519 N i)) : False := by
  classical
  have hexp := exponent_two_of_extremal M2 hB hCiK hn hR0R hR0norm hR0nc hR0exp
  have hRB : Rgrp2519 N i = N.S ⊓ Subgroup.centralizer (N.K : Set G) := inf_eq_right.mpr hB
  have hK0 : N.K0 = N.K := K0_eq_K h (by rw [← hRB]; exact hexp)
  have hSN : N.S ≤ Subgroup.normalizer (N.K : Set G) := by
    have := N.S_le_H.trans N.H_le_normalizer_K0
    rwa [hK0] at this
  have hSC : N.SC = Rgrp2519 N i := by
    unfold Notation25.SC
    rw [hK0, hRB]
  obtain ⟨hRRx, hRxS, hRRxc⟩ := h.concl255
  rw [hSC] at hRRx hRxS hRRxc
  have hxS : N.x ∈ Subgroup.normalizer (N.S : Set G) := N.x_mem.2
  set R := Rgrp2519 N i with hRdef
  set Rx := CFSG.conjugate R N.x with hRxdef
  have hS2 : IsPGroup 2 ↥N.S := N.tuple.sylow.isPGroup
  have hRn : ∀ y ∈ N.S, ∀ r ∈ R, y * r * y⁻¹ ∈ R := by
    intro y hy r hr
    rw [hRB] at hr ⊢
    refine ⟨N.S.mul_mem (N.S.mul_mem hy hr.1) (N.S.inv_mem hy), ?_⟩
    have hyC := mem_normalizer_centralizer_of' (hSN hy)
    exact (Subgroup.mem_normalizer_iff.mp hyC r).mp hr.2
  have hRxn : ∀ y ∈ N.S, ∀ b ∈ Rx, y * b * y⁻¹ ∈ Rx := by
    intro y hy b hb
    rw [hRxdef, BenderBranch.mem_conjugate_iff] at hb ⊢
    have hy' : N.x * y * N.x⁻¹ ∈ N.S := (Subgroup.mem_normalizer_iff.mp hxS y).mp hy
    have e : N.x * (y * b * y⁻¹) * N.x⁻¹ =
        (N.x * y * N.x⁻¹) * (N.x * b * N.x⁻¹) * (N.x * y * N.x⁻¹)⁻¹ := by group
    rw [e]
    exact hRn _ hy' _ hb
  let ρ : ↥N.S →* MulAut ↥N.K := (N.K.normalizerMonoidHom).comp (Subgroup.inclusion hSN)
  have hρ : ∀ (y : ↥N.S) (k : ↥N.K), ((ρ y k : ↥N.K) : G) = (y : G) * (k : G) * (y : G)⁻¹ :=
    fun y k => Subgroup.normalizerMonoidHom_apply_apply_coe N.K ⟨(y : G), hSN y.2⟩ k
  have hker : ∀ y : ↥N.S, ρ y = 1 → (y : G) ∈ R := by
    intro y hy
    rw [hRB]
    refine ⟨y.2, ?_⟩
    show (y : G) ∈ Subgroup.centralizer (N.K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := congrArg (fun φ : MulAut ↥N.K => ((φ ⟨k, hk⟩ : ↥N.K) : G)) hy
    simp only [hρ, MulAut.one_apply] at h1
    have h2 : (y : G) * k = k * (y : G) := by
      calc (y : G) * k = ((y : G) * k * (y : G)⁻¹) * (y : G) := by group
        _ = k * (y : G) := by rw [h1]
    exact h2.symm
  let A : Subgroup ↥N.S := Rx.subgroupOf N.S
  let ρA : ↥A →* MulAut ↥N.K := ρ.comp A.subtype
  let P : Subgroup (MulAut ↥N.K) := ρ.range
  let E : Subgroup (MulAut ↥N.K) := ρA.range
  have hPg : IsPGroup 2 ↥P := IsPGroup.of_surjective hS2 ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hAmem : ∀ b : ↥N.S, b ∈ A ↔ (b : G) ∈ Rx := fun b => Subgroup.mem_subgroupOf
  have hρinj : Function.Injective ρA := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hb1 : ρ (b : ↥N.S) = 1 := hb
    have hR : ((b : ↥N.S) : G) ∈ R := hker _ hb1
    have hRx : ((b : ↥N.S) : G) ∈ Rx := (hAmem _).mp b.2
    have : ((b : ↥N.S) : G) ∈ R ⊓ Rx := ⟨hR, hRx⟩
    rw [hRRx, Subgroup.mem_bot] at this
    exact Subtype.ext (Subtype.ext this)
  have hEn : ∀ g ∈ P, ∀ e ∈ E, g * e * g⁻¹ ∈ E := by
    rintro _ ⟨y, rfl⟩ _ ⟨b, rfl⟩
    refine ⟨⟨y * (b : ↥N.S) * y⁻¹, (hAmem _).mpr ?_⟩, ?_⟩
    · exact hRxn _ y.2 _ ((hAmem _).mp b.2)
    · show ρ (y * (b : ↥N.S) * y⁻¹) = ρ y * ρ (b : ↥N.S) * (ρ y)⁻¹
      simp [map_mul, map_inv]
  have hsq : ∀ e ∈ E, e * e = 1 := by
    rintro _ ⟨b, rfl⟩
    have hb : ((b : ↥N.S) : G) ∈ Rx := (hAmem _).mp b.2
    rw [hRxdef, BenderBranch.mem_conjugate_iff] at hb
    have h1 := hexp _ hb
    have h2 : ((b : ↥N.S) : G) * ((b : ↥N.S) : G) = 1 := by
      have e : ((b : ↥N.S) : G) * ((b : ↥N.S) : G) =
          N.x⁻¹ * ((N.x * (b : G) * N.x⁻¹) * (N.x * (b : G) * N.x⁻¹)) * N.x := by group
      rw [e, h1]
      group
    have h3 : (b : ↥N.S) * (b : ↥N.S) = 1 := Subtype.ext h2
    show ρ (b : ↥N.S) * ρ (b : ↥N.S) = 1
    rw [← map_mul, h3, map_one]
  have hR8 : 8 ≤ Nat.card ↥R := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (Rgrp2519_isPGroup N i)
    rw [hk] at hbig ⊢
    have hk3 : 3 ≤ k := by
      by_contra hcon
      have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
  have hE8 : 8 ≤ Nat.card ↥E := by
    have h1 : Nat.card ↥E = Nat.card ↥A := (Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv).symm
    have h2 : Nat.card ↥A = Nat.card ↥Rx :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRxS).toEquiv
    have h3 : Nat.card ↥Rx = Nat.card ↥R := card_conjugate R N.x
    rw [h1, h2, h3]
    exact hR8
  have hlow := hfin P E hPg hEn hsq hE8
  set Zx : Subgroup G := Rx ⊓ centerOf N.S with hZx
  let Zs : Subgroup ↥N.S := Zx.subgroupOf N.S
  have hZxS : Zx ≤ N.S := inf_le_left.trans hRxS
  have hsub : E ⊓ Subgroup.centralizer (P : Set (MulAut ↥N.K)) ≤ Zs.map ρ := by
    rintro _ ⟨⟨b, rfl⟩, hbc⟩
    refine ⟨(b : ↥N.S), ?_, rfl⟩
    have hbRx : ((b : ↥N.S) : G) ∈ Rx := (hAmem _).mp b.2
    refine Subgroup.mem_subgroupOf.mpr ⟨hbRx, (b : ↥N.S).2, ?_⟩
    show ((b : ↥N.S) : G) ∈ Subgroup.centralizer (N.S : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hc := Subgroup.mem_centralizer_iff.mp hbc (ρ ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
    have h1 : ρ ((⟨y, hy⟩ : ↥N.S) * (b : ↥N.S) * (⟨y, hy⟩ : ↥N.S)⁻¹ * (b : ↥N.S)⁻¹) = 1 := by
      have : ρ (⟨y, hy⟩ : ↥N.S) * ρ (b : ↥N.S) = ρ (b : ↥N.S) * ρ (⟨y, hy⟩ : ↥N.S) := hc
      simp only [map_mul, map_inv]
      rw [this]
      simp
    have h2 := hker _ h1
    have h3 : y * (b : G) * y⁻¹ * (b : G)⁻¹ ∈ Rx := by
      have := hRxn y hy _ hbRx
      exact Rx.mul_mem this (Rx.inv_mem hbRx)
    have h4 : y * (b : G) * y⁻¹ * (b : G)⁻¹ ∈ R ⊓ Rx := ⟨h2, h3⟩
    rw [hRRx, Subgroup.mem_bot] at h4
    have h5 : y * (b : G) = (b : G) * y := by
      have := mul_inv_eq_one.mp h4
      exact (mul_inv_eq_iff_eq_mul.mp this)
    exact h5
  have hZsmap : Nat.card ↥(Zs.map ρ) ≤ Nat.card ↥Zs :=
    Nat.card_le_card_of_surjective _ (ρ.subgroupMap_surjective Zs)
  have hZs : Nat.card ↥Zs = Nat.card ↥Zx :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZxS).toEquiv
  have hZx : Zx ≤ (centerOf N.S ⊓ N.SC).map (MulAut.conj N.x⁻¹).toMonoidHom := by
    intro b hb
    have hbRx : b ∈ Rx := hb.1
    have hbZ : b ∈ centerOf N.S := hb.2
    have hr : N.x * b * N.x⁻¹ ∈ R := by
      have := hbRx
      rw [hRxdef, BenderBranch.mem_conjugate_iff] at this
      exact this
    have hrZ : N.x * b * N.x⁻¹ ∈ centerOf N.S := by
      have := inv_conj_mem_centerOf (S := N.S) (y := N.x⁻¹) (w := b)
        ((Subgroup.normalizer (N.S : Set G)).inv_mem hxS) hbZ
      simpa using this
    refine ⟨N.x * b * N.x⁻¹, ⟨hrZ, by rw [hSC]; exact hr⟩, ?_⟩
    simp [mul_assoc]
  have hup : Nat.card ↥Zx ≤ 2 :=
    (Subgroup.card_le_of_le hZx).trans
      ((Subgroup.card_map_of_injective (MulAut.conj N.x⁻¹).injective).le.trans
        (card_centerOf_inf_SC_le_two h))
  have := Subgroup.card_le_of_le hsub
  omega

end Extremal

end CFSG.QuasithinUnique.Id2519.HS4
