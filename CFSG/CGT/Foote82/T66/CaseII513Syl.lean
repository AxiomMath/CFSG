module

public import CFSG.CGT.Foote82.T66.CaseII513Odd
import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Dih0
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicCoverAbstract
public import CFSG.CGT.Foote82.T66.CaseIISylow

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel

namespace CaseII

section General

variable {Γ : Type*} [Group Γ]

theorem eq_one_or_eq_of_mem_zpowers {u y : Γ} (hu : u * u = 1) (hy : y ∈ Subgroup.zpowers u) :
    y = 1 ∨ y = u := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have h2 : u ^ (2 : ℕ) = 1 := by rw [sq, hu]
  have e : u ^ n = u ^ (n % 2) := by
    have := zpow_eq_zpow_emod' n h2
    simpa using this
  rw [e]
  rcases Int.emod_two_eq_zero_or_one n with h | h <;> rw [h]
  · left
    exact zpow_zero u
  · right
    exact zpow_one u

theorem sup_zpowers_le_centralizer {A : Subgroup Γ} {r s : Γ}
    (hr : r ∈ Subgroup.centralizer (A : Set Γ)) (hs : s ∈ Subgroup.centralizer (A : Set Γ)) :
    Subgroup.zpowers r ⊔ Subgroup.zpowers s ≤ Subgroup.centralizer (A : Set Γ) :=
  sup_le (Subgroup.zpowers_le.2 hr) (Subgroup.zpowers_le.2 hs)

end General

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {G L : Subgroup (GLV V)} {z : GLV V} {v : V} {H₁ : Subgroup (GLV V)}
  {ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)}

theorem mem_commSpace_iff_of_comm {a k : GLV V} (ha : a * a = 1) (hk : k * a = a * k) (w : V) :
    w ∈ commSpace (Subgroup.zpowers a) ⊤ ↔ k w ∈ commSpace (Subgroup.zpowers a) ⊤ := by
  have hka : ∀ x : V, k (a x) = a (k x) := fun x => by
    have := congrArg (fun f : GLV V => f x) hk
    exact this
  have hka' : ∀ x : V, k⁻¹ (a x) = a (k⁻¹ x) := fun x => by
    have hk' : k⁻¹ * a = a * k⁻¹ := by
      calc k⁻¹ * a = k⁻¹ * (a * k) * k⁻¹ := by group
        _ = k⁻¹ * (k * a) * k⁻¹ := by rw [hk]
        _ = a * k⁻¹ := by group
    have := congrArg (fun f : GLV V => f x) hk'
    exact this
  rw [commSpace_zpowers_top_eq_range ha]
  constructor
  · rintro ⟨w', rfl⟩
    refine ⟨k w', ?_⟩
    rw [subOne_apply, subOne_apply, map_sub, hka]
  · rintro ⟨w', hw'⟩
    refine ⟨k⁻¹ w', ?_⟩
    rw [subOne_apply] at hw' ⊢
    rw [← hka', ← map_sub, hw']
    exact k.symm_apply_apply w

abbrev PA (S : Subgroup (GLV V)) (u : GLV V) : Subgroup (GLV V) := S ⊔ Subgroup.zpowers u

abbrev PB (r s : GLV V) : Subgroup (GLV V) := Subgroup.zpowers r ⊔ Subgroup.zpowers s

structure SD (c : Ctx G L z v H₁ ψ) (g r s : GLV V) (S : Subgroup (GLV V)) : Prop where
  r_mem : r ∈ L
  s_mem : s ∈ L
  orderOf_r : orderOf r = 4
  s_mul_s : s * s = 1
  srs : s * r * s⁻¹ = r⁻¹
  s_not_mem : s ∉ Subgroup.zpowers r
  r_comm : r * (g * z * g⁻¹) = (g * z * g⁻¹) * r
  s_comm : s * (g * z * g⁻¹) = (g * z * g⁻¹) * s
  S_le : S ≤ G ⊓ Subgroup.centralizer (L : Set (GLV V))
  S_le_Cz : S ≤ Subgroup.centralizer ({z} : Set (GLV V))
  isPGroup_S : IsPGroup 2 S
  z_mem : z ∈ S
  u_conj : ∀ k ∈ S, (g * z * g⁻¹) * k * (g * z * g⁻¹)⁻¹ ∈ S
  uniq : ∀ k ∈ S, orderOf k = 2 → k = z
  cent_u : ∀ k ∈ S, k * (g * z * g⁻¹) = (g * z * g⁻¹) * k → k = 1 ∨ k = z
  u_not_mem : g * z * g⁻¹ ∉ S
  inf_eq : PA S (g * z * g⁻¹) ⊓ PB r s = ⊥
  comm : ∀ a ∈ PA S (g * z * g⁻¹), ∀ b ∈ PB r s, a * b = b * a
  card_PA : Nat.card ↥(PA S (g * z * g⁻¹)) = 2 * Nat.card ↥S
  card_P : Nat.card ↥(PA S (g * z * g⁻¹) ⊔ PB r s) = 16 * Nat.card ↥S
  P_le : PA S (g * z * g⁻¹) ⊔ PB r s ≤ G ⊓ Subgroup.centralizer ({z} : Set (GLV V))
  sylow : ∀ Y : Subgroup (GLV V), Y ≤ G ⊓ Subgroup.centralizer ({z} : Set (GLV V)) →
    IsPGroup 2 Y → Nat.card ↥Y ≤ 16 * Nat.card ↥S

namespace GD

variable {c : Ctx G L z v H₁ ψ} {g : GLV V} (d : GD c g)
include d

theorem cent_u_of (hs : CaseIISplit) (haut : CaseIIAut) (hG1 : CaseIIG1) {S : Subgroup (GLV V)}
    (hSK : S ≤ G ⊓ Subgroup.centralizer (L : Set (GLV V)))
    (hSz : S ≤ Subgroup.centralizer ({z} : Set (GLV V))) (hS2 : IsPGroup 2 S) (hzS : z ∈ S)
    {k : GLV V} (hk : k ∈ S) (hku : k * (g * z * g⁻¹) = (g * z * g⁻¹) * k) : k = 1 ∨ k = z := by
  have hkG : k ∈ G := (hSK hk).1
  have hkz : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.1 (hSz hk)
  have hxU : ∀ w, w ∈ UU z (g * z * g⁻¹) ↔ k w ∈ UU z (g * z * g⁻¹) := by
    intro w
    simp only [UU, Submodule.mem_inf]
    rw [mem_commSpace_iff_of_comm c.z_mul_z hkz w,
      mem_commSpace_iff_of_comm d.u_mul_u hku w]
  have hkN := d.mem_normalizer_H hs hkG hxU
  obtain ⟨h₁, hh₁, hconj⟩ := c.exists_H₁_of_normalizer haut hkN
  have hh₁L : ∀ l ∈ L, h₁ * l = l * h₁ := by
    intro l hl
    have h1 := hconj l (c.L_le_H hl)
    have h2 : k * l * k⁻¹ = l := by
      rw [← Subgroup.mem_centralizer_iff.1 (hSK hk).2 l hl, mul_inv_cancel_right]
    rw [h2] at h1
    calc h₁ * l = (h₁ * l * h₁⁻¹) * h₁ := by group
      _ = l * h₁ := by rw [← h1]
  have hcH : h₁⁻¹ * k ∈ G ⊓ Subgroup.centralizer (HH G L v : Set (GLV V)) := by
    refine ⟨G.mul_mem (G.inv_mem (c.H₁_le_G hh₁)) hkG, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro y hy
    have h1 := hconj y hy
    calc y * (h₁⁻¹ * k) = h₁⁻¹ * (h₁ * y * h₁⁻¹) * k := by group
      _ = h₁⁻¹ * (k * y * k⁻¹) * k := by rw [h1]
      _ = h₁⁻¹ * k * y := by group
  have hodd := d.odd_card_CH hG1
  rcases c.eq_one_or_eq_z hG1 hh₁ hh₁L with h | h
  · left
    rw [h, inv_one, one_mul] at hcH
    exact eq_one_of_isPGroup_of_odd hS2 hodd hk hcH
  · right
    rw [h] at hcH
    have h1 := eq_one_of_isPGroup_of_odd hS2 hodd (S.mul_mem (S.inv_mem hzS) hk) hcH
    have : k = z * (z⁻¹ * k) := by group
    rw [this, h1, mul_one]

theorem eq_one_of_mem_center (ad : ∃ α : ↥L →* ↥(alternatingGroup (Fin 6)),
      ∃ β : ↥(commSpace L ⊤) →+ altHeart 6, AD L α β)
    {y : GLV V} (hyL : y ∈ L) (hyC : y ∈ Subgroup.centralizer (L : Set (GLV V))) : y = 1 := by
  obtain ⟨α, β, ad⟩ := ad
  have hL := c.data.L_iso
  set e := ad.αe hL
  have hcen : e ⟨y, hyL⟩ ∈ Subgroup.center ↥(alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro σ
    obtain ⟨l, rfl⟩ := e.surjective σ
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 hyC l l.2
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hcen
  have : (⟨y, hyL⟩ : ↥L) = 1 := e.injective (hcen.trans (map_one e).symm)
  exact congrArg Subtype.val this

theorem exists_sd (hs : CaseIISplit) (haut : CaseIIAut) (hG1 : CaseIIG1) :
    ∃ r s : GLV V, ∃ S : Subgroup (GLV V), SD c g r s S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, β, ad⟩ := c.exists_ad hs
  have hL := c.data.L_iso
  obtain ⟨r, s, hrL, hsL, hr4, hss, hsrs, hsr, hru, hsu⟩ := d.exists_rs hs hG1 ad hL
  set u := g * z * g⁻¹ with hu
  have hu2 : u * u = 1 := d.u_mul_u
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  set Cz := G ⊓ Subgroup.centralizer ({z} : Set (GLV V)) with hCz
  have hLCz : ∀ l ∈ L, l ∈ Cz := fun l hl =>
    ⟨c.L_le_G hl, Subgroup.mem_centralizer_singleton_iff.2 (c.comm_z hl)⟩
  have huCz : u ∈ Cz := d.u_mem_Cz
  have hzCz : z ∈ Cz := ⟨c.z_mem_G, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hCzN : Cz ≤ Subgroup.normalizer (L : Set (GLV V)) := c.centralizer_le_normalizer
  set P₂ := PB r s with hP₂
  have hP₂L : P₂ ≤ L := sup_le (Subgroup.zpowers_le.2 hrL) (Subgroup.zpowers_le.2 hsL)
  have hP₂card : Nat.card ↥P₂ = 8 :=
    CFSG.GH74.GLS.Stage2.Local.P27.Psp4.card_dihedral_sup 4 r s hr4 hss hsrs hsr
  have hP₂2 : IsPGroup 2 ↥P₂ := IsPGroup.of_card (n := 3) (by rw [hP₂card]; norm_num)
  have hz2 : IsPGroup 2 ↥(Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, c.orderOf_z, pow_one])
  have hu2' : IsPGroup 2 ↥(Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, d.orderOf_u, pow_one])
  have hE2 : IsPGroup 2 ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers u) :=
    IsPGroup.to_sup_of_normal_left' hz2 hu2' (le_normalizer_of_commute fun a ha b hb => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_zpow (show Commute z u from d.comm.symm) m n).eq)
  have hEP₂ : P₂ ≤ Subgroup.centralizer
      ((Subgroup.zpowers z ⊔ Subgroup.zpowers u : Subgroup (GLV V)) : Set (GLV V)) := by
    apply sup_zpowers_le_centralizer
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hc : h ∈ Subgroup.centralizer ({r} : Set (GLV V)) := by
        refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_) hh
        · exact Subgroup.mem_centralizer_singleton_iff.2 (c.comm_z hrL).symm
        · exact Subgroup.mem_centralizer_singleton_iff.2 hru.symm
      exact Subgroup.mem_centralizer_singleton_iff.1 hc
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hc : h ∈ Subgroup.centralizer ({s} : Set (GLV V)) := by
        refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_) hh
        · exact Subgroup.mem_centralizer_singleton_iff.2 (c.comm_z hsL).symm
        · exact Subgroup.mem_centralizer_singleton_iff.2 hsu.symm
      exact Subgroup.mem_centralizer_singleton_iff.1 hc
  have hR₀2 : IsPGroup 2 ↥((Subgroup.zpowers z ⊔ Subgroup.zpowers u) ⊔ P₂) :=
    IsPGroup.to_sup_of_normal_left' hE2 hP₂2 (hEP₂.trans (Subgroup.centralizer_le_normalizer _))
  have hR₀Cz : (Subgroup.zpowers z ⊔ Subgroup.zpowers u) ⊔ P₂ ≤ Cz :=
    sup_le (sup_le (Subgroup.zpowers_le.2 hzCz) (Subgroup.zpowers_le.2 huCz))
      (hP₂L.trans fun l hl => hLCz l hl)
  obtain ⟨Qs, hQs⟩ := (hR₀2.of_equiv (Subgroup.subgroupOfEquivOfLe hR₀Cz).symm).exists_le_sylow
  set Q : Subgroup (GLV V) := (Qs : Subgroup ↥Cz).map Cz.subtype with hQ
  have hQCz : Q ≤ Cz := Subgroup.map_subtype_le _
  have hQ2 : IsPGroup 2 ↥Q := Qs.isPGroup'.map _
  have hR₀Q : (Subgroup.zpowers z ⊔ Subgroup.zpowers u) ⊔ P₂ ≤ Q := by
    intro x hx
    exact ⟨⟨x, hR₀Cz hx⟩, hQs (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hQmax : ∀ Y : Subgroup (GLV V), Y ≤ Cz → IsPGroup 2 ↥Y → Nat.card ↥Y ≤ Nat.card ↥Q := by
    intro Y hYCz hY
    obtain ⟨Ys, hYs⟩ := (hY.of_equiv (Subgroup.subgroupOfEquivOfLe hYCz).symm).exists_le_sylow
    have h1 := Subgroup.card_le_of_le hYs
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYCz).toEquiv] at h1
    rw [hQ, Subgroup.card_map_of_injective Cz.subtype_injective, Sylow.card_eq_multiplicity,
      ← Sylow.card_eq_multiplicity Ys]
    exact h1
  have hzQ : z ∈ Q := hR₀Q (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers z)))
  have huQ : u ∈ Q := hR₀Q (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers u)))
  have hP₂Q : P₂ ≤ Q := le_sup_right.trans hR₀Q
  set S := Q ⊓ Subgroup.centralizer (L : Set (GLV V)) with hS
  have hSK : S ≤ G ⊓ Subgroup.centralizer (L : Set (GLV V)) :=
    fun k hk => ⟨(hQCz hk.1).1, hk.2⟩
  have hSz : S ≤ Subgroup.centralizer ({z} : Set (GLV V)) := fun k hk => (hQCz hk.1).2
  have hS2 : IsPGroup 2 ↥S := hQ2.to_le inf_le_left
  have hzS : z ∈ S := ⟨hzQ, c.z_mem_K.2⟩
  have huN : u ∈ Subgroup.normalizer (L : Set (GLV V)) := d.u_mem_N
  have hu_conj : ∀ k ∈ S, u * k * u⁻¹ ∈ S := by
    intro k hk
    refine ⟨Q.mul_mem (Q.mul_mem huQ hk.1) (Q.inv_mem huQ), ?_⟩
    show u * k * u⁻¹ ∈ Subgroup.centralizer (L : Set (GLV V))
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : u⁻¹ * l * u ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ huN) l).1 hl
      simpa [mul_assoc] using this
    have h1 := Subgroup.mem_centralizer_iff.1 hk.2 _ hl'
    calc l * (u * k * u⁻¹) = u * ((u⁻¹ * l * u) * k) * u⁻¹ := by group
      _ = u * (k * (u⁻¹ * l * u)) * u⁻¹ := by rw [h1]
      _ = u * k * u⁻¹ * l := by group
  have huS : u ∉ S := fun h => d.u_not_mem_centralizer hG1 h.2
  have huNS : u ∈ Subgroup.normalizer (S : Set (GLV V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hu_conj k hk, fun hk => ?_⟩
    have := hu_conj _ hk
    rw [hui] at this
    have e : u * (u * k * u) * u = k := by
      calc u * (u * k * u) * u = (u * u) * k * (u * u) := by group
        _ = k := by rw [hu2, one_mul, mul_one]
    rwa [e] at this
  set P₁ := PA S u with hP₁
  have hP₁card : Nat.card ↥P₁ = 2 * Nat.card ↥S := by
    have h1 := card_sup_mul_card_inf (Subgroup.zpowers_le.2 huNS)
    have hinf : Subgroup.zpowers u ⊓ S = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨hy1, hy2⟩
      rcases eq_one_or_eq_of_mem_zpowers hu2 hy1 with h | h
      · exact h
      · exact absurd (h ▸ hy2) huS
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, d.orderOf_u, sup_comm] at h1
    exact h1
  have hcomm : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a := by
    have hP₂C : P₂ ≤ Subgroup.centralizer (P₁ : Set (GLV V)) := by
      apply sup_zpowers_le_centralizer
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        have hc : h ∈ Subgroup.centralizer ({r} : Set (GLV V)) := by
          refine sup_le (fun k hk => ?_) (Subgroup.zpowers_le.2 ?_) hh
          · exact Subgroup.mem_centralizer_singleton_iff.2
              (Subgroup.mem_centralizer_iff.1 hk.2 r hrL).symm
          · exact Subgroup.mem_centralizer_singleton_iff.2 hru.symm
        exact Subgroup.mem_centralizer_singleton_iff.1 hc
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        have hc : h ∈ Subgroup.centralizer ({s} : Set (GLV V)) := by
          refine sup_le (fun k hk => ?_) (Subgroup.zpowers_le.2 ?_) hh
          · exact Subgroup.mem_centralizer_singleton_iff.2
              (Subgroup.mem_centralizer_iff.1 hk.2 s hsL).symm
          · exact Subgroup.mem_centralizer_singleton_iff.2 hsu.symm
        exact Subgroup.mem_centralizer_singleton_iff.1 hc
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.1 (hP₂C hb) a ha)
  have hSP₁ : S ≤ P₁ := le_sup_left
  have hidx : (S.subgroupOf P₁).index = 2 := by
    have h := (S.subgroupOf P₁).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSP₁).toEquiv, hP₁card] at h
    have hpos : 0 < Nat.card ↥S := Nat.card_pos
    have : Nat.card ↥S * (S.subgroupOf P₁).index = Nat.card ↥S * 2 := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have huP₁ : u ∈ P₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have hinf : P₁ ⊓ P₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    have hyL : y ∈ L := hP₂L hy2
    rw [Subgroup.mem_bot]
    by_cases hyS : y ∈ S
    · exact d.eq_one_of_mem_center ⟨α, β, ad⟩ hyL hyS.2
    · exfalso
      have hyu : y * u ∈ S := by
        have h1 := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨y, hy1⟩) (b := ⟨u, huP₁⟩)).2
          ⟨fun h => absurd (Subgroup.mem_subgroupOf.1 h) hyS,
            fun h => absurd (Subgroup.mem_subgroupOf.1 h) huS⟩
        exact Subgroup.mem_subgroupOf.1 h1
      set k := y * u with hk
      have hyk : y = k * u := by rw [hk, mul_assoc, hu2, mul_one]
      apply d.not_inner hs hG1 ad hL ⟨y, hyL⟩
      intro l
      apply Subtype.ext
      rw [conjL_coe]
      show u * (l : GLV V) * u⁻¹ = y * l * y⁻¹
      have hkL := Subgroup.mem_centralizer_iff.1 hyu.2
      have hu' : u = k⁻¹ * y := by rw [hyk]; group
      have hyl : y * (l : GLV V) * y⁻¹ ∈ L := L.mul_mem (L.mul_mem hyL l.2) (L.inv_mem hyL)
      rw [hu']
      calc k⁻¹ * y * ↑l * (k⁻¹ * y)⁻¹ = k⁻¹ * (y * ↑l * y⁻¹) * k := by group
        _ = k⁻¹ * (k * (y * ↑l * y⁻¹)) := by rw [mul_assoc, hkL _ hyl]
        _ = y * ↑l * y⁻¹ := by group
  have hPcard : Nat.card ↥(P₁ ⊔ P₂) = 16 * Nat.card ↥S := by
    have h1 := card_sup_mul_card_inf (A := P₂) (B := P₁)
      (le_normalizer_of_commute fun a ha b hb => hcomm a ha b hb)
    rw [inf_comm, hinf, Subgroup.card_bot, mul_one, sup_comm, hP₂card, hP₁card] at h1
    rw [h1]
    ring
  have hPQ : P₁ ⊔ P₂ ≤ Q := sup_le (sup_le inf_le_left (Subgroup.zpowers_le.2 huQ)) hP₂Q
  have hQdvd := ad.card_dvd hL hQ2 (hQCz.trans hCzN)
  have hPeq : P₁ ⊔ P₂ = Q := by
    apply Subgroup.eq_of_le_of_card_ge hPQ
    rw [hPcard]
    exact Nat.le_of_dvd (Nat.mul_pos (by norm_num) Nat.card_pos) hQdvd
  refine ⟨r, s, S,
    { r_mem := hrL
      s_mem := hsL
      orderOf_r := hr4
      s_mul_s := hss
      srs := hsrs
      s_not_mem := hsr
      r_comm := hru
      s_comm := hsu
      S_le := hSK
      S_le_Cz := hSz
      isPGroup_S := hS2
      z_mem := hzS
      u_conj := hu_conj
      uniq := ?_
      cent_u := fun k hk hku => d.cent_u_of hs haut hG1 hSK hSz hS2 hzS hk hku
      u_not_mem := huS
      inf_eq := hinf
      comm := hcomm
      card_PA := hP₁card
      card_P := hPcard
      P_le := hPeq ▸ hQCz
      sylow := fun Y hY hY2 => (hQmax Y hY hY2).trans (by rw [← hPeq, hPcard]) }⟩
  intro k hk hk2
  have hrank : CFSG.Open.pRank 2 (G ⊓ Subgroup.centralizer (L : Set (GLV V))) ≤ 1 :=
    c.rank.le
  have hmem := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPCov.mem_zpowers_of_isPGroup_pRank_le_one
    hrank hS2 hSK hzS hk c.orderOf_z hk2
  rcases eq_one_or_eq_of_mem_zpowers c.z_mul_z hmem with h | h
  · rw [h, orderOf_one] at hk2
    exact absurd hk2 (by norm_num)
  · exact h

end GD

end CaseII

end CFSG.CGT.Foote82
