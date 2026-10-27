module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FinalStruct
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FinalZc
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FinalBad

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin A6Facts

section Convert

variable {G : Type} [Group G]

theorem isFourSubgroup_iff {F : Subgroup G} : IsFourSubgroup F ↔ Four F := by
  constructor
  · rintro ⟨⟨hc, hsq⟩, hcard⟩
    refine ⟨⟨fun b hb => ?_, fun b hb b' hb' => ?_⟩, hcard⟩
    · have := hsq b hb
      rwa [pow_two] at this
    · exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥F)).comm ⟨b, hb⟩ ⟨b', hb'⟩)
  · rintro ⟨⟨hsq, hcomm⟩, hcard⟩
    exact ⟨⟨IsMulCommutative.mk (Std.Commutative.mk fun a b => Subtype.ext (hcomm a a.2 b b.2)),
      fun x hx => by rw [pow_two]; exact hsq x hx⟩, hcard⟩

end Convert

section Final

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G} {D : A6Datum N}

theorem A6Datum.card_S (D : A6Datum N) (hK0 : N.K0 = N.K) :
    Nat.card N.S = Nat.card N.SC * 32 := by
  let φ : ↥N.S →* ↥P0 :=
    { toFun := fun s => ⟨D.Φ (s : G), D.S_mem s s.2⟩
      map_one' := Subtype.ext (by simpa using D.Φ_one)
      map_mul' := fun a b => Subtype.ext (by
        simpa using D.mul a (N.S_le_H a.2) b (N.S_le_H b.2)) }
  have hsurj : Function.Surjective φ := by
    intro p
    obtain ⟨s, hs, hsp⟩ := D.S_surj p p.2
    exact ⟨⟨s, hs⟩, Subtype.ext hsp⟩
  have hker : φ.ker = N.SC.subgroupOf N.S := by
    ext s
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact D.mem_SC_of_Φ_eq_one hK0 s.2 (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext (D.Φ_eq_one_of_mem_SC hK0 h)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv, card_P0, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe N.SC_le_S).toEquiv] at h1
  rw [h1, mul_comm]

theorem FinalCtx.card_SK_eq (C : FinalCtx N t zK D) (h2523 : Concl2523 N) :
    Nat.card N.SK = 8 := by
  obtain ⟨E₁, E₂, hE₁K, hE₂K, hE₁4, hE₂4, hne, -, -, -⟩ := h2523
  have hdvd : 4 ∣ Nat.card N.SK := by
    have := Subgroup.card_dvd_of_le hE₁K
    rwa [hE₁4.2] at this
  have hle := C.card_SK_le
  have hne4 : Nat.card N.SK ≠ 4 := by
    intro h4
    apply hne
    have h1 : E₁ = N.SK := Subgroup.eq_of_le_of_card_ge hE₁K (by have := hE₁4.2; omega)
    have h2 : E₂ = N.SK := Subgroup.eq_of_le_of_card_ge hE₂K (by have := hE₂4.2; omega)
    rw [h1, h2]
  have hpos : 0 < Nat.card N.SK := Nat.card_pos
  omega

theorem FinalCtx.exists_finalE (C : FinalCtx N t zK D) {E : Subgroup G} (hEK : E ≤ N.SK)
    (hE4 : IsFourSubgroup E) : ∃ e, FinalE C E e := by
  obtain ⟨hzKE, e, heE, -, -, hrefl, -, hEel⟩ :=
    D.four_subgroup_data C.hK0 C.hsimple C.hf C.hΦzK hEK hE4
  exact ⟨e, ⟨hEK, hzKE, heE, hrefl, hEel⟩⟩

theorem FinalCtx.exists_SKx_of_E4 (C : FinalCtx N t zK D) {e : G} (he : e ∈ N.SK)
    (her : IsRefl (D.Φ e)) {c : P10} (hc : InE4 c) :
    ∃ f ∈ CFSG.conjugate N.SK N.x, D.Φ f = c := by
  obtain ⟨hf1mem, hf1sq, hf1ne, hf1zb, hf1E4⟩ := C.refl_image he her
  set f₁ : G := N.x⁻¹ * e * N.x with hf₁
  set τ : P10 := D.Φ f₁ with hτ
  have hτP : τ ∈ P0 := hf1E4.1
  have hτsq : τ * τ = 1 := P0_sq_of_centralizes_D hτP hf1E4.2
  have hτpsl : τ ∉ A6Models.psl29 := fun hmem => by
    rcases E4_inter_psl29 hf1E4 hmem with h | h
    · exact hf1ne h
    · exact hf1zb h
  obtain ⟨p, hpP, hpτ⟩ : ∃ p ∈ P0, ¬ τ * p = p * τ := by
    by_contra hcon
    push Not at hcon
    rcases center_P0 hτP hcon with h | h
    · exact hf1ne h
    · exact hf1zb h
  obtain ⟨sp, hspS, hspΦ⟩ := D.S_surj p hpP
  have hspH : sp ∈ N.H := N.S_le_H hspS
  have hf₁S : f₁ ∈ N.S := C.SKx_le_S hf1mem
  have hf₁H : f₁ ∈ N.H := N.S_le_H hf₁S
  set f₂ : G := sp * f₁ * sp⁻¹ with hf₂
  have hf₂mem : f₂ ∈ CFSG.conjugate N.SK N.x :=
    Subgroup.le_normalizer_iff.mp C.S_le_normalizer_SKx sp hspS f₁ hf1mem
  have hf₂H : f₂ ∈ N.H := N.S_le_H (C.SKx_le_S hf₂mem)
  have hf₂Φ : D.Φ f₂ = p * τ * p⁻¹ := by rw [hf₂, D.Φ_conj hspH hf₁H, hspΦ]
  have hτ'E4 : InE4 (p * τ * p⁻¹) := hf₂Φ ▸ C.inE4_of_SKx hf₂mem
  have hτ'1 : p * τ * p⁻¹ ≠ 1 := by
    intro h
    apply hf1ne
    have : τ = p⁻¹ * (p * τ * p⁻¹) * p := by group
    rw [this, h]
    group
  have hττ' : τ ≠ p * τ * p⁻¹ := by
    intro h
    apply hpτ
    calc τ * p = (p * τ * p⁻¹) * p := by rw [← h]
      _ = p * τ := by group
  have hτ'zb : p * τ * p⁻¹ ≠ zb := by
    intro h
    apply hf1zb
    have h1 : p * τ = p * zb := by
      calc p * τ = (p * τ * p⁻¹) * p := by group
        _ = zb * p := by rw [h]
        _ = p * zb := zb_central p hpP
    exact mul_left_cancel h1
  have hτ'eq : p * τ * p⁻¹ = τ * zb := by
    rcases E4_shape hf1E4 hτpsl hτ'E4 with h | h | h | h
    · exact absurd h hτ'1
    · exact absurd h hτ'zb
    · exact absurd h.symm hττ'
    · exact h
  have hτzb : τ * zb = zb * τ := (zb_central τ hτP).symm
  rcases E4_shape hf1E4 hτpsl hc with h | h | h | h
  · exact ⟨1, (CFSG.conjugate N.SK N.x).one_mem, by rw [D.Φ_one, h]⟩
  · refine ⟨f₁ * f₂, (CFSG.conjugate N.SK N.x).mul_mem hf1mem hf₂mem, ?_⟩
    rw [D.mul f₁ hf₁H f₂ hf₂H, hf₂Φ, hτ'eq, h]
    calc τ * (τ * zb) = (τ * τ) * zb := by group
      _ = zb := by rw [hτsq, one_mul]
  · exact ⟨f₁, hf1mem, h.symm⟩
  · exact ⟨f₂, hf₂mem, by rw [hf₂Φ, hτ'eq, h]⟩

theorem card_SC_eq_four (h : Lv2527 N t zK) (D : A6Datum N) : Nat.card N.SC = 4 := by
  have hK0 : N.K0 = N.K := h.concl2520
  obtain ⟨E, e, C, hE, hE4, -⟩ := FinalCtx.exists_E h D
  have hconj : ∀ a ∈ N.SC, N.x⁻¹ * a * N.x ∈ N.S := by
    intro a ha
    have : N.x⁻¹ * a * N.x ∈ CFSG.conjugate N.SC N.x := by
      rw [BenderBranch.mem_conjugate_iff]
      have e : N.x * (N.x⁻¹ * a * N.x) * N.x⁻¹ = a := by group
      rw [e]; exact ha
    exact h.concl255.2.1 this
  let ι : ↥N.SC →* P10 :=
    { toFun := fun a => D.Φ (N.x⁻¹ * (a : G) * N.x)
      map_one' := by simpa using D.Φ_one
      map_mul' := fun a b => by
        have e : N.x⁻¹ * ((a * b : ↥N.SC) : G) * N.x =
            (N.x⁻¹ * (a : G) * N.x) * (N.x⁻¹ * (b : G) * N.x) := by
          simp only [Subgroup.coe_mul]; group
        simp only [e]
        exact D.mul _ (N.S_le_H (hconj a a.2)) _ (N.S_le_H (hconj b b.2)) }
  have hinj : Function.Injective ι := by
    intro a b hab
    have hx1 : N.x⁻¹ * (a : G) * N.x ∈ N.S := hconj a a.2
    have hx2 : N.x⁻¹ * (b : G) * N.x ∈ N.S := hconj b b.2
    have h1 := D.inv_mul_mem_SC hK0 hx1 hx2 hab
    have hmem2 : (N.x⁻¹ * (a : G) * N.x)⁻¹ * (N.x⁻¹ * (b : G) * N.x) ∈
        CFSG.conjugate N.SC N.x := by
      rw [BenderBranch.mem_conjugate_iff]
      have e : N.x * ((N.x⁻¹ * (a : G) * N.x)⁻¹ * (N.x⁻¹ * (b : G) * N.x)) * N.x⁻¹ =
          (a : G)⁻¹ * b := by group
      rw [e]
      exact N.SC.mul_mem (N.SC.inv_mem a.2) b.2
    have h3 : (N.x⁻¹ * (a : G) * N.x)⁻¹ * (N.x⁻¹ * (b : G) * N.x) ∈
        N.SC ⊓ CFSG.conjugate N.SC N.x := ⟨h1, hmem2⟩
    rw [h.concl255.1, Subgroup.mem_bot] at h3
    have h4 : N.x⁻¹ * (a : G) * N.x = N.x⁻¹ * (b : G) * N.x := inv_mul_eq_one.mp h3
    apply Subtype.ext
    calc (a : G) = N.x * (N.x⁻¹ * (a : G) * N.x) * N.x⁻¹ := by group
      _ = N.x * (N.x⁻¹ * (b : G) * N.x) * N.x⁻¹ := by rw [h4]
      _ = b := by group
  have hP : ∀ a : ↥N.SC, ι a ∈ P0 := fun a => D.S_mem _ (hconj a a.2)
  have hZ : ∀ a : ↥N.SC, ∀ c, InE4 c → ι a * c = c * ι a := by
    intro a c hc
    obtain ⟨f, hf, hfΦ⟩ := C.exists_SKx_of_E4 (hE.hEK hE.heE) hE.hrefl hc
    have hfb : N.x * f * N.x⁻¹ ∈ N.SK := BenderBranch.mem_conjugate_iff.mp hf
    have hcomm : (a : G) * (N.x * f * N.x⁻¹) = (N.x * f * N.x⁻¹) * (a : G) := by
      have := Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer a.2) _ (hK0 ▸ hfb.2)
      exact this.symm
    have hax : (N.x⁻¹ * (a : G) * N.x) * f = f * (N.x⁻¹ * (a : G) * N.x) := by
      calc (N.x⁻¹ * (a : G) * N.x) * f
          = N.x⁻¹ * ((a : G) * (N.x * f * N.x⁻¹)) * N.x := by group
        _ = N.x⁻¹ * ((N.x * f * N.x⁻¹) * (a : G)) * N.x := by rw [hcomm]
        _ = f * (N.x⁻¹ * (a : G) * N.x) := by group
    have hfH : f ∈ N.H := N.S_le_H (C.SKx_le_S hf)
    have haH : N.x⁻¹ * (a : G) * N.x ∈ N.H := N.S_le_H (hconj a a.2)
    show D.Φ (N.x⁻¹ * (a : G) * N.x) * c = c * D.Φ (N.x⁻¹ * (a : G) * N.x)
    set a' : G := N.x⁻¹ * (a : G) * N.x with ha'
    have e1 : D.Φ (a' * f) = D.Φ a' * D.Φ f := D.mul _ haH _ hfH
    have e2 : D.Φ (f * a') = D.Φ f * D.Φ a' := D.mul _ hfH _ haH
    calc D.Φ a' * c = D.Φ a' * D.Φ f := by rw [hfΦ]
      _ = D.Φ (a' * f) := e1.symm
      _ = D.Φ (f * a') := by rw [hax]
      _ = D.Φ f * D.Φ a' := e2
      _ = c * D.Φ a' := by rw [hfΦ]
  rcases h.concl2527 with h4 | h8 | hq8
  · obtain ⟨e4⟩ := h4
    rw [Nat.card_congr e4.toEquiv]
    simp
  · exfalso
    obtain ⟨e8⟩ := h8
    let u : Multiplicative (ZMod 8) := Multiplicative.ofAdd 1
    have hu : u * u * (u * u) ≠ 1 := by decide
    let g : ↥N.SC := e8.symm u
    have hg : g * g * (g * g) ≠ 1 := by
      intro h1
      apply hu
      have := congrArg e8 h1
      simpa [g] using this
    apply hg
    apply hinj
    simp only [map_mul, map_one]
    exact zc_fourth_perm (hP g) (hZ g)
  · exfalso
    obtain ⟨eq8⟩ := hq8
    have q1 : (QuaternionGroup.a 1 * QuaternionGroup.a 1 : QuaternionGroup 2) ≠ 1 := by decide
    have q2 : (QuaternionGroup.a 1 * QuaternionGroup.a 1 : QuaternionGroup 2) =
        QuaternionGroup.xa 0 * QuaternionGroup.xa 0 := by decide
    have q3 : (QuaternionGroup.a 1 * QuaternionGroup.a 1 : QuaternionGroup 2) =
        (QuaternionGroup.a 1 * QuaternionGroup.xa 0) * (QuaternionGroup.a 1 * QuaternionGroup.xa 0) := by
      decide
    let a : ↥N.SC := eq8.symm (QuaternionGroup.a 1)
    let b : ↥N.SC := eq8.symm (QuaternionGroup.xa 0)
    have h1 : a * a ≠ 1 := by
      intro h1
      apply q1
      have := congrArg eq8 h1
      simpa [a] using this
    have h2 : a * a = b * b := by
      have := congrArg eq8.symm q2
      simpa only [a, b, map_mul] using this
    have h3 : a * a = a * b * (a * b) := by
      have := congrArg eq8.symm q3
      simpa only [a, b, map_mul] using this
    refine zc_no_q8_perm (hP a) (hP b) (hZ a) (hZ b) ?_ ?_ ?_
    · intro h4
      apply h1
      apply hinj
      simpa only [map_mul, map_one] using h4
    · have := congrArg ι h2
      simpa only [map_mul] using this
    · have := congrArg ι h3
      simpa only [map_mul] using this

theorem FinalCtx.badCtx (h : Lv2527 N t zK) (C : FinalCtx N t zK D) {E : Subgroup G} {e : G}
    (hE : FinalE C E e) (hE4 : IsFourSubgroup E)
    (hbad : N.x * N.x ∉ Subgroup.normalizer (E : Set G)) :
    ∃ E' : Subgroup G, BadCtx N.S N.SK N.x E E' := by
  obtain ⟨E₁, E₂, hE₁K, hE₂K, hE₁4, hE₂4, hne, hall, -, -⟩ := h.concl2523
  have hEE : E = E₁ ∨ E = E₂ := hall E hE.hEK hE4
  obtain ⟨E', hE'K, hE'4, hne', hall'⟩ : ∃ E' : Subgroup G, E' ≤ N.SK ∧ IsFourSubgroup E' ∧
      E' ≠ E ∧ ∀ F : Subgroup G, F ≤ N.SK → IsFourSubgroup F → F = E ∨ F = E' := by
    rcases hEE with h1 | h1
    · refine ⟨E₂, hE₂K, hE₂4, ?_, fun F hF hF4 => ?_⟩
      · rw [h1]; exact hne.symm
      · rcases hall F hF hF4 with h2 | h2
        · left; rw [h2, h1]
        · right; exact h2
    · refine ⟨E₁, hE₁K, hE₁4, ?_, fun F hF hF4 => ?_⟩
      · rw [h1]; exact hne
      · rcases hall F hF hF4 with h2 | h2
        · right; exact h2
        · left; rw [h2, h1]
  have hnonab : ∃ a ∈ N.SK, ∃ b ∈ N.SK, a * b ≠ b * a := by
    obtain ⟨d, d', hd, hdpsl, hd', hd'psl, hdd⟩ := exists_noncomm_D
    obtain ⟨a, ha, rfl⟩ := D.exists_mem_SK C.hKH C.h254 C.hsimple hd hdpsl
    obtain ⟨a', ha', rfl⟩ := D.exists_mem_SK C.hKH C.h254 C.hsimple hd' hd'psl
    refine ⟨a, ha, a', ha', fun hcomm => hdd ?_⟩
    have haH := N.S_le_H (N.SK_le_S ha)
    have ha'H := N.S_le_H (N.SK_le_S ha')
    rw [← D.mul a haH a' ha'H, ← D.mul a' ha'H a haH, hcomm]
  refine ⟨E', ?_⟩
  exact
    { two := ⟨fun s hs a ha =>
          Subgroup.le_normalizer_iff.mp (N.S_le_normalizer_SK C.hKH) s hs a ha,
        hE.hEK, hE'K, isFourSubgroup_iff.mp hE4, isFourSubgroup_iff.mp hE'4, hne',
        fun F hF hF4 => hall' F hF (isFourSubgroup_iff.mpr hF4)⟩
      hSKS := N.SK_le_S
      hxN := N.x_mem.2
      hx2 := by simpa [sq] using N.x_sq
      hSKxS := fun b hb => C.SKx_le_S hb
      hcomm := C.comm_SK_SKx
      hdisj := C.SK_inf_SKx
      hnonab := hnonab
      hcard8 := C.card_SK_eq h.concl2523
      hNS := fun s hs hsN => mem_normalizer_of_conj_mem (C.normS_conj hE hs hsN)
      hS128 := by
        have h1 := D.card_S C.hK0
        have h2 := card_SC_eq_four h D
        omega
      hbad := hbad }

theorem bad_case_T_le (h : Lv2527 N t zK) (D : A6Datum N) (C : FinalCtx N t zK D) {E : Subgroup G}
    {e : G} (hE : FinalE C E e) (hE4 : IsFourSubgroup E)
    (hpair : IsUStarPair M N.H (N.S ⊓ Subgroup.normalizer (E : Set G))
      (N.H ⊓ Subgroup.normalizer (E : Set G)))
    (hbad : N.x * N.x ∉ Subgroup.normalizer (E : Set G)) :
    T ≤ Subgroup.normalizer (N.S : Set G) := by
  obtain ⟨E', C'⟩ := C.badCtx h hE hE4 hbad
  have hS2 : IsPGroup 2 ↥N.S := N.tuple.sylow.isPGroup
  have hAS : E ⊔ CFSG.conjugate E N.x ≤ N.S := by
    refine sup_le (fun y hy => N.SK_le_S (hE.hEK hy)) (fun g hg => ?_)
    have h1 : N.x * g * N.x⁻¹ ∈ E := BenderBranch.mem_conjugate_iff.mp hg
    have h2 := N.x_conj_S' (N.SK_le_S (hE.hEK h1))
    simpa [mul_assoc] using h2
  have hA2 : IsPGroup 2 ↥(E ⊔ CFSG.conjugate E N.x) := hS2.to_le hAS
  have hc := ((h.concl2512 C.hKH).1 _ _ hpair inf_le_left).2
  have hres := hc (E ⊔ CFSG.conjugate E N.x) hA2 (C.z_mem_A hE) (C.A_le hE) (C.norm_H_le hE)
  have hQA : N.S ⊓ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((E ⊔ CFSG.conjugate E N.x : Subgroup G) : Set G) := fun g hg =>
    C.norm_H_le hE ⟨N.S_le_H hg.1, hg.2⟩
  exact C'.T_le_normalizer hs.setting.sylow.isPGroup N.S_le_T N.x_mem.1 N.x_not_mem
    h.concl2513.1.1 hQA (fun P hQP hPN hP2 => hres.2.eq_of_le hQP hPN hP2)

end Final

end CFSG.QuasithinUnique
