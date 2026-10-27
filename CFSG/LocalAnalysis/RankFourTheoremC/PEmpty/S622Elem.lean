module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem s622_inverts_of_centralizer_trivial {G : Type} [Group G] [Finite G] {D : Subgroup G}
    {y : G} (hy2 : y ^ 2 = 1) (hyD : ∀ d ∈ D, y * d * y⁻¹ ∈ D)
    (h : ∀ d ∈ D, y * d = d * y → d = 1) :
    (∀ e ∈ D, y * e * y⁻¹ = e⁻¹) ∧ ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
  have hyy : y * y = 1 := by simpa [pow_two] using hy2
  let φ : D →* D :=
    { toFun := fun d => ⟨y * d * y⁻¹, hyD d d.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hfix : MonoidHom.FixedPointFree φ := by
    intro d hd
    have hd' : y * d * y⁻¹ = d := congrArg Subtype.val hd
    exact Subtype.ext (h d d.2 (by rwa [mul_inv_eq_iff_eq_mul] at hd'))
  have hinv : Function.Involutive φ := by
    intro d
    ext
    show y * (y * (d : G) * y⁻¹) * y⁻¹ = d
    calc y * (y * (d : G) * y⁻¹) * y⁻¹ = (y * y) * d * (y * y)⁻¹ := by group
      _ = d := by rw [hyy]; simp
  refine ⟨fun e he => ?_, fun a ha b hb => ?_⟩
  · exact congrArg (fun f => ((f ⟨e, he⟩ : D) : G)) (hfix.coe_eq_inv_of_involutive hinv)
  · exact congrArg Subtype.val (hfix.commute_all_of_involutive hinv ⟨a, ha⟩ ⟨b, hb⟩)

theorem s622_exists_center_preimage {G : Type} [Group G] {D L : Subgroup G}
    (hDn : ∀ d k : G, d ∈ D → k ∈ L → k * d * k⁻¹ ∈ D) :
    ∃ Z : Subgroup G, ∀ z : G, z ∈ Z ↔ z ∈ L ∧ ∀ l ∈ L, z * l * z⁻¹ * l⁻¹ ∈ D :=
  ⟨{ carrier := {z | z ∈ L ∧ ∀ l ∈ L, z * l * z⁻¹ * l⁻¹ ∈ D}
     one_mem' := ⟨L.one_mem, fun l _ => by simpa using D.one_mem⟩
     mul_mem' := by
       rintro a b ⟨haL, ha⟩ ⟨hbL, hb⟩
       refine ⟨L.mul_mem haL hbL, fun l hl => ?_⟩
       have e : a * b * l * (a * b)⁻¹ * l⁻¹ =
           (a * (b * l * b⁻¹ * l⁻¹) * a⁻¹) * (a * l * a⁻¹ * l⁻¹) := by group
       rw [e]
       exact D.mul_mem (hDn _ a (hb l hl) haL) (ha l hl)
     inv_mem' := by
       rintro a ⟨haL, ha⟩
       refine ⟨L.inv_mem haL, fun l hl => ?_⟩
       have e : a⁻¹ * l * a⁻¹⁻¹ * l⁻¹ = a⁻¹ * (a * l * a⁻¹ * l⁻¹)⁻¹ * a⁻¹⁻¹ := by group
       rw [e]
       exact hDn _ a⁻¹ (D.inv_mem (ha l hl)) (L.inv_mem haL) }, fun _ => Iff.rfl⟩

theorem s622_centralizer_ne_bot {G : Type} [Group G] [Finite G] {D L : Subgroup G} {y : G}
    (hD : Odd (Nat.card D)) (hD1 : D ≠ ⊥) (hL : S622IsSimpleSection L D) (hyL : y ∈ L)
    (hy2 : y ^ 2 = 1) (hy1 : y ∉ D) : ∃ d ∈ D, d ≠ 1 ∧ y * d = d * y := by
  obtain ⟨hDL, hDn, -, hsimp, hnab⟩ := hL
  have hDn' : ∀ d k : G, d ∈ D → k ∈ L → k * d * k⁻¹ ∈ D :=
    (Subgroup.normal_subgroupOf_iff hDL).mp hDn
  have hsimp' : ∀ N : Subgroup G, D ≤ N → N ≤ L →
      (∀ n k : G, n ∈ N → k ∈ L → k * n * k⁻¹ ∈ N) → N = D ∨ N = L :=
    fun N h1 h2 h3 => hsimp N h1 h2 ((Subgroup.normal_subgroupOf_iff h2).mpr h3)
  by_contra hcon
  have h : ∀ d ∈ D, y * d = d * y → d = 1 := by
    intro d hd hc
    by_contra hne
    exact hcon ⟨d, hd, hne, hc⟩
  obtain ⟨hinv, hab⟩ := s622_inverts_of_centralizer_trivial hy2 (fun d hd => hDn' d y hd hyL) h
  have hyy : y * y = 1 := by simpa [pow_two] using hy2
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hCsimp : L ⊓ centralizer (D : Set G) = D ∨ L ⊓ centralizer (D : Set G) = L := by
    refine hsimp' _ ?_ inf_le_left ?_
    · intro d hd
      refine Subgroup.mem_inf.mpr ⟨hDL hd, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact hab e he d hd
    · intro n k hn hk
      obtain ⟨hnL, hnc⟩ := Subgroup.mem_inf.mp hn
      refine Subgroup.mem_inf.mpr ⟨L.mul_mem (L.mul_mem hk hnL) (L.inv_mem hk), ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hnc ⊢
      intro e he
      have he' : k⁻¹ * e * k ∈ D := by simpa using hDn' e k⁻¹ he (L.inv_mem hk)
      have hnk := hnc _ he'
      calc e * (k * n * k⁻¹) = k * ((k⁻¹ * e * k) * n) * k⁻¹ := by group
        _ = k * (n * (k⁻¹ * e * k)) * k⁻¹ := by rw [hnk]
        _ = (k * n * k⁻¹) * e := by group
  rcases hCsimp with hCD | hCL
  ·
    have hcomm : ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ D := by
      intro l hl
      have hmem : l * y * l⁻¹ * y⁻¹ ∈ L ⊓ centralizer (D : Set G) := by
        refine Subgroup.mem_inf.mpr
          ⟨L.mul_mem (L.mul_mem (L.mul_mem hl hyL) (L.inv_mem hl)) (L.inv_mem hyL), ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        have h1 : y⁻¹ * e * y = e⁻¹ := by
          have := hinv e he
          rw [hyi] at this ⊢
          exact this
        have he₂ : l⁻¹ * e⁻¹ * l ∈ D := by
          simpa using hDn' e⁻¹ l⁻¹ (D.inv_mem he) (L.inv_mem hl)
        have key : (l * y * l⁻¹ * y⁻¹) * e * (l * y * l⁻¹ * y⁻¹)⁻¹ = e := by
          calc (l * y * l⁻¹ * y⁻¹) * e * (l * y * l⁻¹ * y⁻¹)⁻¹
              = l * (y * (l⁻¹ * (y⁻¹ * e * y) * l) * y⁻¹) * l⁻¹ := by group
            _ = l * (y * (l⁻¹ * e⁻¹ * l) * y⁻¹) * l⁻¹ := by rw [h1]
            _ = l * (l⁻¹ * e⁻¹ * l)⁻¹ * l⁻¹ := by rw [hinv _ he₂]
            _ = e := by group
        exact (mul_inv_eq_iff_eq_mul.mp key).symm
      rwa [hCD] at hmem
    obtain ⟨Z, hZ⟩ := s622_exists_center_preimage hDn'
    have hZsimp : Z = D ∨ Z = L := by
      refine hsimp' Z ?_ ?_ ?_
      · intro d hd
        rw [hZ]
        refine ⟨hDL hd, fun l hl => ?_⟩
        have e : d * l * d⁻¹ * l⁻¹ = d * (l * d⁻¹ * l⁻¹) := by group
        rw [e]
        exact D.mul_mem hd (hDn' d⁻¹ l (D.inv_mem hd) hl)
      · intro z hz
        exact ((hZ z).mp hz).1
      · intro n k hn hk
        rw [hZ] at hn ⊢
        obtain ⟨hnL, hn⟩ := hn
        refine ⟨L.mul_mem (L.mul_mem hk hnL) (L.inv_mem hk), fun l hl => ?_⟩
        have h1 := hn (k⁻¹ * l * k) (L.mul_mem (L.mul_mem (L.inv_mem hk) hl) hk)
        have e : (k * n * k⁻¹) * l * (k * n * k⁻¹)⁻¹ * l⁻¹ =
            k * (n * (k⁻¹ * l * k) * n⁻¹ * (k⁻¹ * l * k)⁻¹) * k⁻¹ := by group
        rw [e]
        exact hDn' _ k h1 hk
    rcases hZsimp with hZD | hZL
    · apply hy1
      have hyZ : y ∈ Z := by
        rw [hZ]
        refine ⟨hyL, fun l hl => ?_⟩
        have e : y * l * y⁻¹ * l⁻¹ = (l * y * l⁻¹ * y⁻¹)⁻¹ := by group
        rw [e]
        exact D.inv_mem (hcomm l hl)
      rwa [hZD] at hyZ
    · apply hnab
      intro a ha b hb
      have haZ : a ∈ Z := by
        rw [hZL]
        exact ha
      exact ((hZ a).mp haZ).2 b hb
  ·
    have hyC : y ∈ L ⊓ centralizer (D : Set G) := by
      rw [hCL]
      exact hyL
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hyC
    apply hD1
    rw [eq_bot_iff]
    intro e he
    rw [Subgroup.mem_bot]
    exact h e he (hyC.2 e he).symm

theorem s622_exists_omega_center {G : Type} [Group G] (R : Subgroup G) :
    ∃ R₁ : Subgroup G, ∀ x : G, x ∈ R₁ ↔ x ∈ R ∧ (∀ s ∈ R, x * s = s * x) ∧ x ^ 2 = 1 :=
  ⟨{ carrier := {x | x ∈ R ∧ (∀ s ∈ R, x * s = s * x) ∧ x ^ 2 = 1}
     one_mem' := ⟨R.one_mem, fun s _ => by simp, by simp⟩
     mul_mem' := by
       rintro a b ⟨haR, hac, ha2⟩ ⟨hbR, hbc, hb2⟩
       refine ⟨R.mul_mem haR hbR, fun s hs => ?_, ?_⟩
       · rw [mul_assoc, hbc s hs, ← mul_assoc, hac s hs, mul_assoc]
       · rw [(show Commute a b from hac b hbR).mul_pow, ha2, hb2, one_mul]
     inv_mem' := by
       rintro a ⟨haR, hac, ha2⟩
       refine ⟨R.inv_mem haR, fun s hs => ?_, ?_⟩
       · exact (show Commute a s from hac s hs).inv_left
       · rw [inv_pow, ha2, inv_one] }, fun _ => Iff.rfl⟩

theorem s622_exists_central_elemAbelian {G : Type} [Group G] [Finite G] {R : Subgroup G}
    (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    ∃ R₁ : Subgroup G, R₁ ≠ ⊥ ∧ R₁ ≤ R ∧ CFSG.Open.IsElemAbelian 2 R₁ ∧
      (∀ g ∈ normalizer (R : Set G), g ∈ normalizer (R₁ : Set G)) := by
  obtain ⟨R₁, hmem⟩ := s622_exists_omega_center R
  refine ⟨R₁, ?_, fun x hx => ((hmem x).mp hx).1,
    ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun x hx => ((hmem x).mp hx).2.2⟩, ?_⟩
  ·
    haveI : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR1
    haveI := hR.center_nontrivial
    have hcard : 1 < Nat.card (Subgroup.center R) :=
      Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    have hdvd : 2 ∣ Nat.card (Subgroup.center R) :=
      ((hR.to_subgroup (Subgroup.center R)).card_eq_or_dvd).resolve_left (by omega)
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    have hw1 : ((w : R) : G) ≠ 1 := by
      intro h1
      have : w = 1 := Subtype.ext (Subtype.ext h1)
      rw [this, orderOf_one] at hw
      omega
    have hw2 : ((w : R) : G) ^ 2 = 1 := by
      have : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
      exact congrArg (fun u : Subgroup.center R => (((u : R) : G))) this
    have hwR : ((w : R) : G) ∈ R₁ := by
      rw [hmem]
      refine ⟨(w : R).2, fun s hs => ?_, hw2⟩
      have := Subgroup.mem_center_iff.mp w.2 ⟨s, hs⟩
      exact (congrArg Subtype.val this).symm
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hwR
    exact hw1 hwR
  · exact ((hmem a).mp a.2).2.1 b (((hmem b).mp b.2).1)
  · intro g hg
    have key : ∀ g ∈ normalizer (R : Set G), ∀ x ∈ R₁, g * x * g⁻¹ ∈ R₁ := by
      intro g hg x hx
      have hgR : ∀ h : G, h ∈ R ↔ g * h * g⁻¹ ∈ R :=
        fun h => Subgroup.mem_set_normalizer_iff.mp hg h
      obtain ⟨hxR, hxc, hx2⟩ := (hmem x).mp hx
      rw [hmem]
      refine ⟨(hgR x).mp hxR, fun s hs => ?_, ?_⟩
      · have hs' : g⁻¹ * s * g ∈ R := by
          rw [hgR, show g * (g⁻¹ * s * g) * g⁻¹ = s by group]
          exact hs
        calc (g * x * g⁻¹) * s = g * (x * (g⁻¹ * s * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * s * g) * x) * g⁻¹ := by rw [hxc _ hs']
          _ = s * (g * x * g⁻¹) := by group
      · calc (g * x * g⁻¹) ^ 2 = g * (x * x) * g⁻¹ := by rw [pow_two]; group
          _ = 1 := by rw [← pow_two, hx2]; group
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · exact key g hg h
    · intro hgh
      have := key g⁻¹ (inv_mem hg) (g * h * g⁻¹) hgh
      simpa [mul_assoc] using this

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
