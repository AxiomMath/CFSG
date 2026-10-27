module

public import CFSG.CGT.T75F.E710QuotCore
public import CFSG.Walter.Bender1970.S3.TransitivityTools

public section

namespace CFSG.CGT.T75F

open CFSG.CGT.Timmesfeld75

variable {X : Type} [Group X] [Finite X] {D : Set X} {M L : Subgroup X} {q : ℕ}

namespace Endgame710

variable (h : Endgame710 D M L q)
include h

theorem center_quot_eq_bot : Subgroup.center (X ⧸ Subgroup.center X) = ⊥ := by
  rw [eq_bot_iff]
  intro zh hzh
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective zh
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  have hζ : ∀ x : X, z * x * z⁻¹ * x⁻¹ ∈ Subgroup.center X := by
    intro x
    rw [← QuotientGroup.eq_one_iff]
    have hxz := Subgroup.mem_center_iff.1 hzh (QuotientGroup.mk x)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    set x' : X ⧸ Subgroup.center X := QuotientGroup.mk x with hx'
    set z' : X ⧸ Subgroup.center X := QuotientGroup.mk z with hz'
    calc z' * x' * z'⁻¹ * x'⁻¹ = (x' * z') * z'⁻¹ * x'⁻¹ := by rw [hxz]
      _ = 1 := by group
  have hstep : ∀ β ∈ D, z * β * z⁻¹ ∈ D ∧ (β ∈ M → z * β * z⁻¹ ∈ M) ∧
      z * (z * β * z⁻¹) * z⁻¹ = β := by
    intro β hβ
    have hD' : z * β * z⁻¹ ∈ D := h.conj_mem β hβ z
    set ζ := z * β * z⁻¹ * β⁻¹ with hζdef
    have hcen : ∀ g : X, g * ζ = ζ * g := Subgroup.mem_center_iff.1 (hζ β)
    have hzbz : z * β * z⁻¹ = ζ * β := by rw [hζdef]; group
    have hβ2 := h.sq_eq_one β hβ
    have hζsq : ζ * ζ = 1 := by
      have hdz : (z * β * z⁻¹) * (z * β * z⁻¹) = 1 := h.sq_eq_one _ hD'
      rw [hzbz] at hdz
      calc ζ * ζ = ζ * ζ * (β * β) := by rw [hβ2, mul_one]
        _ = ζ * (ζ * β) * β := by group
        _ = ζ * (β * ζ) * β := by rw [hcen β]
        _ = (ζ * β) * (ζ * β) := by group
        _ = 1 := hdz
    refine ⟨hD', fun hβM => ?_, ?_⟩
    · refine h.H3 β hβ hβM _ hD' ?_
      rw [hzbz]
      calc ζ * β * β = (β * ζ) * β := by rw [hcen β]
        _ = β * (ζ * β) := by group
    · have hcz : z * ζ * z⁻¹ = ζ := by rw [hcen z]; group
      calc z * (z * β * z⁻¹) * z⁻¹ = z * (ζ * β) * z⁻¹ := by rw [hzbz]
        _ = (z * ζ * z⁻¹) * (z * β * z⁻¹) := by group
        _ = ζ * (ζ * β) := by rw [hcz, hzbz]
        _ = (ζ * ζ) * β := by group
        _ = β := by rw [hζsq, one_mul]
  let f : ↥(D ∩ (M : Set X) : Set X) → ↥(D ∩ (M : Set X) : Set X) := fun β =>
    ⟨z * β * z⁻¹, (hstep β β.2.1).1, (hstep β β.2.1).2.1 β.2.2⟩
  have hf : ∀ β, f (f β) = β := fun β => Subtype.ext (hstep β β.2.1).2.2
  obtain ⟨⟨β₀, hβ₀⟩, hfix⟩ := exists_fixed_of_involutive f hf h.odd_card_delta
  have hfix' : z * β₀ * z⁻¹ = β₀ := congrArg Subtype.val hfix
  exact h.commute_D_of_fixed hzh hβ₀.1 hfix'

theorem normal_pGroup_quot_eq_bot (V : Subgroup (X ⧸ Subgroup.center X)) [hV : V.Normal]
    (hp : IsPGroup 2 V) : V = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hMS⟩ := h.exists_sylow
  obtain ⟨γ, hγD, hγM, hγfix⟩ := h.exists_fixed S hMS
  have hψ : Function.Surjective (QuotientGroup.mk' (Subgroup.center X)) :=
    QuotientGroup.mk'_surjective _
  let Ŝ : Sylow 2 (X ⧸ Subgroup.center X) := S.mapSurjective hψ
  have hVS : V ≤ Ŝ := hp.le_sylow_of_normal Ŝ
  have hV_fix : ∀ v ∈ V, v * QuotientGroup.mk γ * v⁻¹ = QuotientGroup.mk γ := by
    intro v hv
    have hv' : v ∈ (S : Subgroup X).map (QuotientGroup.mk' (Subgroup.center X)) := by
      have h1 : v ∈ (Ŝ : Subgroup (X ⧸ Subgroup.center X)) := hVS hv
      have h2 : (Ŝ : Subgroup (X ⧸ Subgroup.center X)) =
          (S : Subgroup X).map (QuotientGroup.mk' (Subgroup.center X)) :=
        Sylow.coe_mapSurjective hψ S
      rwa [h2] at h1
    obtain ⟨s, hs, hsv⟩ := hv'
    subst hsv
    change (QuotientGroup.mk s : X ⧸ Subgroup.center X) * QuotientGroup.mk γ *
      (QuotientGroup.mk s)⁻¹ = QuotientGroup.mk γ
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hγfix s hs]
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  have hv_center : v ∈ Subgroup.center (X ⧸ Subgroup.center X) := by
    refine h.mem_center_quot_of_commute fun x hx => ?_
    obtain ⟨d, hd, rfl⟩ := hx
    obtain ⟨g, c, hc, hdeq⟩ := h.single_class hγD hd
    have hc1 : (QuotientGroup.mk c : X ⧸ Subgroup.center X) = 1 := (QuotientGroup.eq_one_iff c).2 hc
    set g' : X ⧸ Subgroup.center X := QuotientGroup.mk g with hg'
    set γ' : X ⧸ Subgroup.center X := QuotientGroup.mk γ with hγ'
    have hdhat : (QuotientGroup.mk' (Subgroup.center X)) d = g' * γ' * g'⁻¹ := by
      change (QuotientGroup.mk d : X ⧸ Subgroup.center X) = g' * γ' * g'⁻¹
      rw [hdeq]
      simp [hg', hγ', hc1]
    rw [hdhat]
    have hw : g'⁻¹ * v * g' ∈ V := by simpa using hV.conj_mem v hv g'⁻¹
    have hf := hV_fix _ hw
    have hf' : (g'⁻¹ * v * g') * γ' = γ' * (g'⁻¹ * v * g') := by
      have := congrArg (fun z => z * (g'⁻¹ * v * g')) hf
      simpa [mul_assoc] using this
    calc (g' * γ' * g'⁻¹) * v = g' * (γ' * (g'⁻¹ * v * g')) * g'⁻¹ := by group
      _ = g' * ((g'⁻¹ * v * g') * γ') * g'⁻¹ := by rw [← hf']
      _ = v * (g' * γ' * g'⁻¹) := by group
  have := h.center_quot_eq_bot ▸ hv_center
  exact Subgroup.mem_bot.1 this

theorem Mhat_comm {a b : X ⧸ Subgroup.center X} (ha : a ∈ Mhat M) (hb : b ∈ Mhat M) :
    a * b = b * a := by
  obtain ⟨m₁, hm₁, rfl⟩ := Subgroup.mem_map.1 ha
  obtain ⟨m₂, hm₂, rfl⟩ := Subgroup.mem_map.1 hb
  change (QuotientGroup.mk m₁ : X ⧸ Subgroup.center X) * QuotientGroup.mk m₂ =
    QuotientGroup.mk m₂ * QuotientGroup.mk m₁
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h.M_comm m₁ hm₁ m₂ hm₂]

theorem Mhat_sq {a : X ⧸ Subgroup.center X} (ha : a ∈ Mhat M) : a * a = 1 := by
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 ha
  change (QuotientGroup.mk m : X ⧸ Subgroup.center X) * QuotientGroup.mk m = 1
  rw [← QuotientGroup.mk_mul, h.M_sq m hm]
  rfl

theorem Mhat_le_closure : Mhat M ≤ Subgroup.closure
    ((QuotientGroup.mk' (Subgroup.center X)) '' D ∩ (Mhat M : Set (X ⧸ Subgroup.center X))) := by
  have hmap : Mhat M = Subgroup.closure
      ((QuotientGroup.mk' (Subgroup.center X)) '' (D ∩ (M : Set X))) := by
    unfold Mhat
    conv_lhs => rw [← h.M_gen]
    exact MonoidHom.map_closure _ _
  rw [hmap]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨d, hd, rfl⟩
  refine ⟨⟨d, hd.1, rfl⟩, ?_⟩
  rw [← hmap]
  exact Subgroup.mem_map.2 ⟨d, hd.2, rfl⟩

theorem odd_normal_quot_eq_bot (R : Subgroup (X ⧸ Subgroup.center X)) [hR : R.Normal]
    (hodd : Odd (Nat.card R)) : R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ := QuotientGroup.mk' (Subgroup.center X) with hψdef
  have hLinj : ∀ l ∈ L, ψ l = 1 → l = 1 := fun l hl h1 => by
    by_contra hne
    exact h.not_mem_center (h.L_D l hl hne) ((QuotientGroup.eq_one_iff l).1 h1)
  set Lh : Subgroup (X ⧸ Subgroup.center X) := L.map ψ with hLh
  have hLhcard : Nat.card Lh = q ^ 2 := by
    have hbij : Function.Bijective (fun l : L => (⟨ψ (l : X), l, l.2, rfl⟩ : Lh)) := by
      constructor
      · intro a b hab
        apply Subtype.ext
        have hab' : ψ (a : X) = ψ (b : X) := congrArg Subtype.val hab
        have h1 : ψ ((a : X)⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab', inv_mul_cancel]
        have h2 : (a : X)⁻¹ * b ∈ L := L.mul_mem (L.inv_mem a.2) b.2
        exact inv_mul_eq_one.1 (hLinj _ h2 h1)
      · rintro ⟨_, l, hl, rfl⟩
        exact ⟨⟨l, hl⟩, rfl⟩
    exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm.trans h.L_card
  have hLhcomm : IsMulCommutative Lh := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain ⟨la, hla, rfl⟩ := ha
    obtain ⟨lb, hlb, rfl⟩ := hb
    apply Subtype.ext
    change ψ la * ψ lb = ψ lb * ψ la
    rw [← map_mul, ← map_mul, h.M_comm la (h.L_le hla) lb (h.L_le hlb)]
  have hLhexp : ∀ x ∈ Lh, x ^ 2 = 1 := by
    rintro _ ⟨l, hl, rfl⟩
    rw [← map_pow, pow_two, h.M_sq l (h.L_le hl), map_one]
  have hLhge : 2 ^ 2 ≤ Nat.card Lh := by
    rw [hLhcard]
    have := h.q_ge
    nlinarith
  have hcop : ¬ 2 ∣ Nat.card R := by
    obtain ⟨c, hc⟩ := hodd
    omega
  have hgen := CFSG.Walter.le_iSup_inf_centralizer (E := Lh) (N := R) Nat.prime_two hLhcomm
    hLhexp hLhge Subgroup.le_normalizer_of_normal hcop
  have hMR : ∀ x ∈ Mhat M, x ∈ R → x = 1 := by
    intro x hxM hxR
    have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h.Mhat_sq hxM)
    have h2 : orderOf x ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R hxR
    have h3 : orderOf x ∣ Nat.gcd 2 (Nat.card R) := Nat.dvd_gcd h1 h2
    have h4 : Nat.gcd 2 (Nat.card R) = 1 := (Nat.coprime_two_left.2 hodd)
    rw [h4] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  have hcent : ∀ e ∈ Lh, e ≠ 1 → R ⊓ Subgroup.centralizer ({e} : Set (X ⧸ Subgroup.center X)) ≤
      Subgroup.centralizer ((Mhat M : Subgroup (X ⧸ Subgroup.center X)) : Set _) := by
    intro e he he1 r hr
    have hrR : r ∈ R := (Subgroup.mem_inf.1 hr).1
    have hrc : r * e = e * r :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hr).2
    obtain ⟨l, hl, rfl⟩ := he
    have hl1 : l ≠ 1 := fun h' => he1 (by rw [h', map_one])
    have heD : ψ l ∈ ψ '' D := ⟨l, h.L_D l hl hl1, rfl⟩
    have heM : ψ l ∈ Mhat M := Subgroup.mem_map.2 ⟨l, h.L_le hl, rfl⟩
    have hrc' : r⁻¹ * ψ l = ψ l * r⁻¹ := (Commute.inv_left (show Commute r (ψ l) from hrc)).eq
    have hA : ∀ d ∈ ψ '' D, d ∈ Mhat M → r * d * r⁻¹ ∈ Mhat M := by
      intro d hdD hdM
      refine h.H3hat heD heM (h.Dhat_conj hdD r) ?_
      have hcomm : d * ψ l = ψ l * d := h.Mhat_comm hdM heM
      calc r * d * r⁻¹ * ψ l = r * d * (r⁻¹ * ψ l) := by group
        _ = r * d * (ψ l * r⁻¹) := by rw [hrc']
        _ = r * (d * ψ l) * r⁻¹ := by group
        _ = r * (ψ l * d) * r⁻¹ := by rw [hcomm]
        _ = (r * ψ l) * d * r⁻¹ := by group
        _ = (ψ l * r) * d * r⁻¹ := by rw [hrc]
        _ = ψ l * (r * d * r⁻¹) := by group
    have hB : Mhat M ≤ (Mhat M).comap (MulAut.conj r).toMonoidHom := by
      refine le_trans h.Mhat_le_closure ?_
      rw [Subgroup.closure_le]
      intro d hd
      exact hA d hd.1 hd.2
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have hm1 : r * m * r⁻¹ ∈ Mhat M := hB hm
    have hc1 : (r * m * r⁻¹) * m⁻¹ ∈ Mhat M := (Mhat M).mul_mem hm1 ((Mhat M).inv_mem hm)
    have hc2 : (r * m * r⁻¹) * m⁻¹ ∈ R := by
      have : m * r⁻¹ * m⁻¹ ∈ R := hR.conj_mem r⁻¹ (R.inv_mem hrR) m
      have h2 := R.mul_mem hrR this
      rwa [show r * (m * r⁻¹ * m⁻¹) = (r * m * r⁻¹) * m⁻¹ by group] at h2
    have h3 := hMR _ hc1 hc2
    have h4 : r * m = m * r := by
      have := mul_inv_eq_one.1 h3
      calc r * m = r * m * r⁻¹ * r := by group
        _ = m * r := by rw [this]
    exact h4.symm
  have hRM : R ≤ Subgroup.centralizer ((Mhat M : Subgroup (X ⧸ Subgroup.center X)) : Set _) :=
    le_trans hgen (iSup_le fun e => iSup_le fun he => iSup_le fun he1 => hcent e he he1)
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  have hr_center : r ∈ Subgroup.center (X ⧸ Subgroup.center X) := by
    refine h.mem_center_quot_of_commute fun x hx => ?_
    obtain ⟨d, hd, rfl⟩ := hx
    obtain ⟨g, hg⟩ := h.exists_conj_mem hd
    set g' : X ⧸ Subgroup.center X := QuotientGroup.mk g with hg'
    have hmM : ψ (g⁻¹ * d * g) ∈ Mhat M := Subgroup.mem_map.2 ⟨g⁻¹ * d * g, hg, rfl⟩
    have hdeq : ψ d = g' * ψ (g⁻¹ * d * g) * g'⁻¹ := by
      show ψ d = ψ g * ψ (g⁻¹ * d * g) * (ψ g)⁻¹
      rw [map_mul, map_mul, map_inv]
      group
    have hw : g'⁻¹ * r * g' ∈ R := by simpa using hR.conj_mem r hr g'⁻¹
    have hwc := Subgroup.mem_centralizer_iff.1 (hRM hw) _ hmM
    rw [hdeq]
    calc g' * ψ (g⁻¹ * d * g) * g'⁻¹ * r
        = g' * (ψ (g⁻¹ * d * g) * (g'⁻¹ * r * g')) * g'⁻¹ := by group
      _ = g' * ((g'⁻¹ * r * g') * ψ (g⁻¹ * d * g)) * g'⁻¹ := by rw [hwc]
      _ = r * (g' * ψ (g⁻¹ * d * g) * g'⁻¹) := by group
  have := h.center_quot_eq_bot ▸ hr_center
  exact Subgroup.mem_bot.1 this

end Endgame710

end CFSG.CGT.T75F
