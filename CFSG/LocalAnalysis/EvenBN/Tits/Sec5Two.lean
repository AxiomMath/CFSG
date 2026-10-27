module

public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4SevenTwo
public import CFSG.LocalAnalysis.EvenBN.Tits.Model.E32Pairs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits
open CFSG.Quasithin (twoF4H)

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem Hyp.eq_of_fixed_CM
    (hd : d.Hyp) {s : G} (hs : s ∈ d.tG) (hsA : s ∈ d.A)
    (hfix : ∀ x ∈ d.M ⊓ centralizer ({d.t} : Set G), x * s * x⁻¹ = s) :
    s = d.t ∨ s = d.t * d.z := by
  obtain ⟨-, -, h11, h10c, h10, h20c⟩ := hd.orbits_A
  have ht2 := hd.t_mul_self
  have he := hd.t_mul_mem_of_mem_tG (d.liftSub_le _) hs hsA
  have hse : s = d.t * (d.t * s) := by rw [← mul_assoc, ht2, one_mul]
  have hefix : ∀ x ∈ d.M ⊓ centralizer ({d.t} : Set G), x * (d.t * s) * x⁻¹ = d.t * s := by
    intro x hx
    have hxt : x * d.t * x⁻¹ = d.t := by
      rw [mem_centralizer_singleton_iff.1 (mem_inf.1 hx).2, mul_inv_cancel_right]
    calc x * (d.t * s) * x⁻¹ = (x * d.t * x⁻¹) * (x * s * x⁻¹) := by group
      _ = d.t * s := by rw [hxt, hfix x hx]
  have single : ∀ {u : G} {O : Set G}, O = {y | ∃ x ∈ d.M ⊓ centralizer ({d.t} : Set G),
      x * u * x⁻¹ = y} → d.t * s ∈ O → O = {d.t * s} := by
    intro u O hO hmem
    rw [hO] at hmem ⊢
    obtain ⟨c₀, hc₀, hc₀e⟩ := hmem
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 := hefix (x * c₀⁻¹) (mul_mem hx (inv_mem hc₀))
      rw [← hc₀e] at h1
      rw [Set.mem_singleton_iff, ← hc₀e]
      calc x * u * x⁻¹ = x * c₀⁻¹ * (c₀ * u * c₀⁻¹) * (x * c₀⁻¹)⁻¹ := by group
        _ = c₀ * u * c₀⁻¹ := h1
    · intro hy
      rw [Set.mem_singleton_iff.1 hy]
      exact ⟨c₀, hc₀, hc₀e⟩
  by_cases he1 : d.t * s = 1
  · left
    rw [hse, he1, mul_one]
  by_cases hez : d.t * s = d.z
  · right
    rw [hse, hez]
  exfalso
  rcases d.mem_zL_or_vL (fun x hx hx1 => Model.hatE_long_or_short hx hx1) he he1 with hz | hv
  · have hmem : d.t * s ∈ (d.zL ∩ d.A) \ {d.z} := ⟨⟨hz, mem_sup_left he⟩, hez⟩
    have h := single h11.symm hmem
    rw [h, Set.ncard_singleton] at h10c
    omega
  · have hmem : d.t * s ∈ d.vL ∩ d.A := ⟨hv, mem_sup_left he⟩
    have h := single h10.symm hmem
    rw [h, Set.ncard_singleton] at h20c
    omega

theorem Hyp.orbit_eq_tG_A
    (hd : d.Hyp) {s : G} (hs : s ∈ d.tG) (hsA : s ∈ d.A) :
    {y | ∃ m ∈ d.M, m * s * m⁻¹ = y} = d.tG ∩ d.A := by
  obtain ⟨k, hk, hks⟩ := hd.transitive (Or.inl rfl) hs hsA
  ext y
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨g, rfl⟩ := hs
    exact ⟨⟨m * g, by group⟩, (mem_normalizer_iff.1 hm _).1 hsA⟩
  · rintro ⟨hy, hyA⟩
    obtain ⟨n, hn, rfl⟩ := hd.transitive (Or.inl rfl) hy hyA
    refine ⟨n * k⁻¹, mul_mem hn (inv_mem hk), ?_⟩
    rw [← hks]
    group

theorem Hyp.CM_eq
    (hd : d.Hyp) :
    d.M ⊓ centralizer ({d.t} : Set G) = d.M ⊓ centralizer ({d.t * d.z} : Set G) := by
  have hfixz := hd.orbits_A.2.1
  have hle : d.M ⊓ centralizer ({d.t} : Set G) ≤ d.M ⊓ centralizer ({d.t * d.z} : Set G) := by
    intro x hx
    obtain ⟨hxM, hxC⟩ := mem_inf.1 hx
    refine mem_inf.2 ⟨hxM, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := hfixz x hx
    have hxt : x * d.t = d.t * x := mem_centralizer_singleton_iff.1 hxC
    calc x * (d.t * d.z) = (x * d.t) * d.z := by group
      _ = (d.t * x) * d.z := by rw [hxt]
      _ = d.t * (x * d.z * x⁻¹) * x := by group
      _ = d.t * d.z * x := by rw [h1]
  have htA : d.t ∈ d.A := mem_sup_right (mem_zpowers _)
  have hzE : d.z ∈ d.E := mem_liftSub.2 ⟨titsZ, Model.titsZ_mem_hatE, titsZ_mem_titsD,
    d.lift_titsZ⟩
  have htz : d.t * d.z ∈ d.tG := hd.t_mul_mem_tG_of_zL ⟨1, one_mem _, by group⟩
  have htzA : d.t * d.z ∈ d.A := mul_mem htA (mem_sup_left hzE)
  have h1 := card_eq_ncard_conj_mul d.M d.t
  have h2 := card_eq_ncard_conj_mul d.M (d.t * d.z)
  rw [hd.orbit_eq_tG_A ⟨1, by group⟩ htA] at h1
  rw [hd.orbit_eq_tG_A htz htzA] at h2
  have hpos : 0 < (d.tG ∩ d.A).ncard := by
    rw [Set.ncard_pos (Set.toFinite _)]
    exact ⟨d.t, ⟨1, by group⟩, htA⟩
  refine eq_of_le_of_card_ge hle ?_
  have h3 := h1.symm.trans h2
  have := Nat.eq_of_mul_eq_mul_left hpos h3
  rw [this]

theorem Hyp.M_le_centralizer_z
    (hd : d.Hyp) : d.M ≤ centralizer ({d.z} : Set G) := by
  intro m hm
  rw [mem_centralizer_singleton_iff]
  have ht2 := hd.t_mul_self
  have hED : Model.hatE ≤ titsD := Model.hatE_le_titsJ.trans titsJ_le_titsD
  have htA : d.t ∈ d.A := mem_sup_right (mem_zpowers _)
  have hzE : d.z ∈ d.E := mem_liftSub.2 ⟨titsZ, Model.titsZ_mem_hatE, titsZ_mem_titsD,
    d.lift_titsZ⟩
  have htz : d.t * d.z ∈ d.tG := hd.t_mul_mem_tG_of_zL ⟨1, one_mem _, by group⟩
  have htzA : d.t * d.z ∈ d.A := mul_mem htA (mem_sup_left hzE)
  have hz1 : d.z ≠ 1 := fun h => by
    rw [← d.lift_titsZ, ← d.lift_one] at h
    exact titsZ_ne_one (d.lift_inj titsZ_mem_titsD (one_mem _) h)
  set s := m * d.t * m⁻¹ with hs
  set s' := m * (d.t * d.z) * m⁻¹ with hs'
  have hsG : s ∈ d.tG := ⟨m, rfl⟩
  have hsA : s ∈ d.A := (mem_normalizer_iff.1 hm _).1 htA
  have hs'G : s' ∈ d.tG := by
    obtain ⟨g, hg⟩ := htz
    exact ⟨m * g, by rw [hs', ← hg]; group⟩
  have hs'A : s' ∈ d.A := (mem_normalizer_iff.1 hm _).1 htzA
  have hKeq := hd.CM_eq
  have hstab : ∀ x ∈ d.M, x * s * x⁻¹ = s ↔ x * s' * x⁻¹ = s' := by
    intro x hx
    have hy : m⁻¹ * x * m ∈ d.M := mul_mem (mul_mem (inv_mem hm) hx) hm
    have e1 : x * s * x⁻¹ = s ↔ m⁻¹ * x * m ∈ centralizer ({d.t} : Set G) := by
      rw [mem_centralizer_singleton_iff, hs]
      constructor
      · intro h
        calc m⁻¹ * x * m * d.t = m⁻¹ * (x * (m * d.t * m⁻¹) * x⁻¹) * x * m := by group
          _ = d.t * (m⁻¹ * x * m) := by rw [h]; group
      · intro h
        calc x * (m * d.t * m⁻¹) * x⁻¹ = m * (m⁻¹ * x * m * d.t) * (m⁻¹ * x * m)⁻¹ * m⁻¹ := by
              group
          _ = m * d.t * m⁻¹ := by rw [h]; group
    have e2 : x * s' * x⁻¹ = s' ↔ m⁻¹ * x * m ∈ centralizer ({d.t * d.z} : Set G) := by
      rw [mem_centralizer_singleton_iff, hs']
      constructor
      · intro h
        calc m⁻¹ * x * m * (d.t * d.z) = m⁻¹ * (x * (m * (d.t * d.z) * m⁻¹) * x⁻¹) * x * m := by
              group
          _ = d.t * d.z * (m⁻¹ * x * m) := by rw [h]; group
      · intro h
        calc x * (m * (d.t * d.z) * m⁻¹) * x⁻¹ =
            m * (m⁻¹ * x * m * (d.t * d.z)) * (m⁻¹ * x * m)⁻¹ * m⁻¹ := by group
          _ = m * (d.t * d.z) * m⁻¹ := by rw [h]; group
    rw [e1, e2]
    constructor
    · intro h
      have := hKeq ▸ (mem_inf.2 ⟨hy, h⟩ : m⁻¹ * x * m ∈ d.M ⊓ centralizer ({d.t} : Set G))
      exact (mem_inf.1 this).2
    · intro h
      have := hKeq.symm ▸
        (mem_inf.2 ⟨hy, h⟩ : m⁻¹ * x * m ∈ d.M ⊓ centralizer ({d.t * d.z} : Set G))
      exact (mem_inf.1 this).2
  have ha := hd.t_mul_mem_of_mem_tG (d.liftSub_le _) hsG hsA
  have hb := hd.t_mul_mem_of_mem_tG (d.liftSub_le _) hs'G hs'A
  set a := d.t * s with ha_def
  set b := d.t * s' with hb_def
  have hsa : s = d.t * a := by rw [ha_def, ← mul_assoc, ht2, one_mul]
  have hs'b : s' = d.t * b := by rw [hb_def, ← mul_assoc, ht2, one_mul]
  have hss' : s ≠ s' := fun h => hz1 (by
    have h' : m * d.t * m⁻¹ = m * (d.t * d.z) * m⁻¹ := h
    have : d.t = d.t * d.z := by
      have := congrArg (fun y => m⁻¹ * y * m) h'
      simpa [mul_assoc] using this
    calc d.z = d.t⁻¹ * (d.t * d.z) := by group
      _ = 1 := by rw [← this]; group)
  have hK : ∀ y, y ∈ d.tG → y ∈ d.A →
      (∀ x ∈ d.M ⊓ centralizer ({d.t} : Set G), x * y * x⁻¹ = y) → y = d.t ∨ y = d.t * d.z :=
    fun y hy hyA h => hd.eq_of_fixed_CM hy hyA h
  have hKt : ∀ x ∈ d.M ⊓ centralizer ({d.t} : Set G), x * d.t * x⁻¹ = d.t := fun x hx => by
    rw [mem_centralizer_singleton_iff.1 (mem_inf.1 hx).2, mul_inv_cancel_right]
  have hKtz : ∀ x ∈ d.M ⊓ centralizer ({d.t} : Set G), x * (d.t * d.z) * x⁻¹ = d.t * d.z :=
    fun x hx => by
      have hx' := hKeq ▸ hx
      rw [mem_centralizer_singleton_iff.1 (mem_inf.1 hx').2, mul_inv_cancel_right]
  have hab : b = a * d.z := by
    by_cases ha1 : a = 1
    ·
      have hst : s = d.t := by rw [hsa, ha1, mul_one]
      have hmK : m ∈ d.M ⊓ centralizer ({d.t} : Set G) := by
        refine mem_inf.2 ⟨hm, mem_centralizer_singleton_iff.2 ?_⟩
        calc m * d.t = m * d.t * m⁻¹ * m := by group
          _ = d.t * m := by rw [← hs, hst]
      have h1 := hKtz m hmK
      rw [← hs'] at h1
      rw [ha1, one_mul, hb_def, h1, ← mul_assoc, ht2, one_mul]
    by_cases haz : a = d.z
    ·
      have hstz : s = d.t * d.z := by rw [hsa, haz]
      have hfix : ∀ x ∈ d.M ⊓ centralizer ({d.t} : Set G), x * s' * x⁻¹ = s' := fun x hx =>
        (hstab x (mem_inf.1 hx).1).1 (by rw [hstz]; exact hKtz x hx)
      rcases hK s' hs'G hs'A hfix with h | h
      · rw [haz, hb_def, h, ht2, ← d.lift_titsZ, ← d.lift_mul titsZ_mem_titsD titsZ_mem_titsD,
          titsZ_mul_self, d.lift_one]
      · exact absurd (hstz.trans h.symm) hss'
    have hb1 : b ≠ 1 := by
      intro hb1
      have hs't : s' = d.t := by rw [hs'b, hb1, mul_one]
      have hfix : ∀ x ∈ d.M ⊓ centralizer ({d.t} : Set G), x * s * x⁻¹ = s := fun x hx =>
        (hstab x (mem_inf.1 hx).1).2 (by rw [hs't]; exact hKt x hx)
      rcases hK s hsG hsA hfix with h | h
      · exact ha1 (by rw [ha_def, h, ht2])
      · exact haz (by rw [ha_def, h, ← mul_assoc, ht2, one_mul])
    have hbz : b ≠ d.z := by
      intro hbz
      have hs'tz : s' = d.t * d.z := by rw [hs'b, hbz]
      have hfix : ∀ x ∈ d.M ⊓ centralizer ({d.t} : Set G), x * s * x⁻¹ = s := fun x hx =>
        (hstab x (mem_inf.1 hx).1).2 (by rw [hs'tz]; exact hKtz x hx)
      rcases hK s hsG hsA hfix with h | h
      · exact ha1 (by rw [ha_def, h, ht2])
      · exact haz (by rw [ha_def, h, ← mul_assoc, ht2, one_mul])
    have hba : b ≠ a := fun h => hss' (by rw [hsa, hs'b, h])
    by_contra hbaz
    obtain ⟨aa, haa, haaD, haaa⟩ := mem_liftSub.1 ha
    obtain ⟨bb, hbb, hbbD, hbbb⟩ := mem_liftSub.1 hb
    have hne : ∀ {x y : Equiv.Perm (Fin 1755)}, x ∈ titsD → y ∈ titsD →
        d.lift x ≠ d.lift y → x ≠ y := fun _ _ h h' => h (by rw [h'])
    obtain ⟨xx, hxxJ, hxxa, hxxb⟩ := Model.exists_mem_titsJ_comm_conj haa hbb
      (hne haaD (one_mem _) (by rw [haaa, d.lift_one]; exact ha1))
      (hne haaD titsZ_mem_titsD (by rw [haaa, d.lift_titsZ]; exact haz))
      (hne hbbD (one_mem _) (by rw [hbbb, d.lift_one]; exact hb1))
      (hne hbbD titsZ_mem_titsD (by rw [hbbb, d.lift_titsZ]; exact hbz))
      (hne hbbD haaD (by rw [hbbb, haaa]; exact hba))
      (hne hbbD (mul_mem haaD titsZ_mem_titsD) (by
        rw [hbbb, d.lift_mul haaD titsZ_mem_titsD, haaa, d.lift_titsZ]; exact hbaz))
    have hxxD : xx ∈ titsD := titsJ_le_titsD hxxJ
    set x := d.lift xx with hx
    have hxC : x ∈ centralizer ({d.t} : Set G) := hd.L_le (d.lift_mem xx)
    have hxM : x ∈ d.M := by
      have hρ : (d.ρ ⟨x, hxC⟩ : Equiv.Perm (Fin 1755)) = xx := hd.ρ_lift hxxD
      refine (hd.mem_normalizer_tSup_iff hED hxC).2 ?_
      rw [hρ]
      exact Model.twoF4H_le_normalizer_hatE
        (CFSG.Quasithin.le_extSub (titsJ_le_titsH hxxJ))
    have hxa : x * a * x⁻¹ = a := by
      rw [← haaa, hx, ← d.lift_conj hxxD haaD, hxxa, mul_inv_cancel_right]
    have hxb : x * b * x⁻¹ = b * d.z := by
      rw [← hbbb, hx, ← d.lift_conj hxxD hbbD, hxxb, d.lift_mul hbbD titsZ_mem_titsD,
        d.lift_titsZ]
    have hxt : x * d.t * x⁻¹ = d.t := by
      rw [mem_centralizer_singleton_iff.1 hxC, mul_inv_cancel_right]
    have hxs : x * s * x⁻¹ = s := by
      rw [hsa]
      calc x * (d.t * a) * x⁻¹ = (x * d.t * x⁻¹) * (x * a * x⁻¹) := by group
        _ = d.t * a := by rw [hxt, hxa]
    have hxs' := (hstab x hxM).1 hxs
    rw [hs'b] at hxs'
    have h1 : x * (d.t * b) * x⁻¹ = d.t * (b * d.z) := by
      calc x * (d.t * b) * x⁻¹ = (x * d.t * x⁻¹) * (x * b * x⁻¹) := by group
        _ = d.t * (b * d.z) := by rw [hxt, hxb]
    rw [h1] at hxs'
    exact hz1 (by
      have := mul_left_cancel hxs'
      calc d.z = b⁻¹ * (b * d.z) := by group
        _ = 1 := by rw [this]; group)
  have hmz : m * d.z * m⁻¹ = s⁻¹ * s' := by rw [hs, hs']; group
  have h1 : s⁻¹ * s' = a⁻¹ * b := by rw [hsa, hs'b]; group
  have h2 : m * d.z * m⁻¹ = d.z := by rw [hmz, h1, hab]; group
  calc m * d.z = m * d.z * m⁻¹ * m := by group
    _ = d.z * m := by rw [h2]

theorem Hyp.thm52
    (hd : d.Hyp) {m : G} (hm : m ∈ d.M) {s : G} (hs : d.t * s ∈ d.E) :
    d.t * (m * s * m⁻¹) ∈ d.E ∧ m * (s * d.z) * m⁻¹ = m * s * m⁻¹ * d.z := by
  have hmz := mem_centralizer_singleton_iff.1 (hd.M_le_centralizer_z hm)
  have hmE : m ∈ normalizer (d.E : Set G) := by
    have h := hd.M_le_normalizer hm
    rwa [hd.A_inf_L] at h
  refine ⟨?_, ?_⟩
  ·
    have htA : d.t ∈ d.A := mem_sup_right (mem_zpowers _)
    have h1 := hd.t_mul_mem_of_mem_tG (d.liftSub_le _) (s := m * d.t * m⁻¹) ⟨m, rfl⟩
      ((mem_normalizer_iff.1 hm _).1 htA)
    have h2 := (mem_normalizer_iff.1 hmE _).1 hs
    have ht2 := hd.t_mul_self
    have e : d.t * (m * s * m⁻¹) = d.t * (m * d.t * m⁻¹) * (m * (d.t * s) * m⁻¹) := by
      calc d.t * (m * s * m⁻¹) = d.t * (m * (d.t * d.t) * s * m⁻¹) := by rw [ht2, mul_one]
        _ = d.t * (m * d.t * m⁻¹) * (m * (d.t * s) * m⁻¹) := by group
    rw [e]
    exact mul_mem h1 h2
  · calc m * (s * d.z) * m⁻¹ = m * s * m⁻¹ * (m * d.z * m⁻¹) := by group
      _ = m * s * m⁻¹ * d.z := by rw [hmz, mul_inv_cancel_right]

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
