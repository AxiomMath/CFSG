module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15Xprime

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.Open CFSG.Quasithin

@[expose] def centSKz {G : Type} [Group G] (S K : Subgroup G) (zK : G) : Subgroup G :=
  S ⊓ Subgroup.centralizer (threeCoreCent K zK : Set G)

section Generic

variable {G : Type} [Group G]

theorem mem_centSKz_iff {S K : Subgroup G} {zK r : G} :
    r ∈ centSKz S K zK ↔ r ∈ S ∧ ∀ v ∈ threeCoreCent K zK, v * r = r * v := by
  unfold centSKz
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact Iff.rfl

end Generic

section Config

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  (N : Notation25 hs) {t zK : G}

theorem inner_mem_SC_mul_SK (h : Lv2513 N t zK) (F : K33Facts N.K) {s : G} (hs' : s ∈ N.S)
    (hin : Ch1.InducesInner s N.K) : ∃ c ∈ N.SC, ∃ k ∈ N.SK, s = c * k := by
  have hKH := H_le_normalizer_K N h F
  have hsimple : IsSimpleGroup ↥N.K := h.facts258.simple
  have hZK : ∀ x ∈ N.K, (∀ y ∈ N.K, x * y = y * x) → x = 1 := fun x hx hc =>
    N.center_K_trivial hsimple hx hc
  have hK0 : N.K0 = N.K := N.K0_eq hKH
  have hSN : ∀ s ∈ N.S, s ∈ Subgroup.normalizer (N.K : Set G) := fun s hs' =>
    N.S_le_normalizer_K hKH hs'
  let W : Subgroup G :=
    { carrier := {l | l ∈ N.K ∧ ∃ s ∈ N.S, ∀ x ∈ N.K, s⁻¹ * x * s = l⁻¹ * x * l}
      mul_mem' := by
        rintro a b ⟨haK, s₁, hs₁, h₁⟩ ⟨hbK, s₂, hs₂, h₂⟩
        refine ⟨N.K.mul_mem haK hbK, s₁ * s₂, N.S.mul_mem hs₁ hs₂, ?_⟩
        intro x hx
        have hxa : a⁻¹ * x * a ∈ N.K := N.K.mul_mem (N.K.mul_mem (N.K.inv_mem haK) hx) haK
        calc (s₁ * s₂)⁻¹ * x * (s₁ * s₂) = s₂⁻¹ * (s₁⁻¹ * x * s₁) * s₂ := by group
          _ = s₂⁻¹ * (a⁻¹ * x * a) * s₂ := by rw [h₁ x hx]
          _ = b⁻¹ * (a⁻¹ * x * a) * b := h₂ _ hxa
          _ = (a * b)⁻¹ * x * (a * b) := by group
      one_mem' := ⟨N.K.one_mem, 1, N.S.one_mem, fun x _ => by group⟩
      inv_mem' := by
        rintro a ⟨haK, s, hs₁, h₁⟩
        refine ⟨N.K.inv_mem haK, s⁻¹, N.S.inv_mem hs₁, ?_⟩
        intro x hx
        have hsx : s * x * s⁻¹ ∈ N.K := (Subgroup.mem_normalizer_iff.mp (hSN s hs₁) x).mp hx
        have h3 := h₁ _ hsx
        have e1 : s⁻¹ * (s * x * s⁻¹) * s = x := by group
        rw [e1] at h3
        have h2 : s * x * s⁻¹ = a * x * a⁻¹ := by
          calc s * x * s⁻¹ = a * (a⁻¹ * (s * x * s⁻¹) * a) * a⁻¹ := by group
            _ = a * x * a⁻¹ := by rw [← h3]
        simpa using h2 }
  have hWK : W ≤ N.K := fun l hl => hl.1
  have hW2 : IsPGroup 2 W := by
    rintro ⟨l, hlK, s, hsS, hlact⟩
    have hc : ∀ x ∈ N.K, (s * l⁻¹) * x = x * (s * l⁻¹) := by
      intro x hx
      have h1 := hlact x hx
      calc s * l⁻¹ * x = s * (l⁻¹ * x * l) * l⁻¹ := by group
        _ = s * (s⁻¹ * x * s) * l⁻¹ := by rw [h1]
        _ = x * (s * l⁻¹) := by group
    have hsl : s * l = l * s := by
      have h3 : s = l * (s * l⁻¹) := by
        calc s = (s * l⁻¹) * l := by group
          _ = l * (s * l⁻¹) := hc l hlK
      calc s * l = l * (s * l⁻¹) * l := by rw [← h3]
        _ = l * s := by group
    obtain ⟨m, hm⟩ := N.tuple.sylow.isPGroup ⟨s, hsS⟩
    have hsm : s ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hcomm : Commute s l⁻¹ := (show Commute s l from hsl).inv_right
    have hpow : (s * l⁻¹) ^ 2 ^ m = (l⁻¹) ^ 2 ^ m := by rw [hcomm.mul_pow, hsm, one_mul]
    have hlm : (l⁻¹) ^ 2 ^ m ∈ N.K := N.K.pow_mem (N.K.inv_mem hlK) _
    have hlcen : ∀ y ∈ N.K, (l⁻¹) ^ 2 ^ m * y = y * (l⁻¹) ^ 2 ^ m := by
      intro y hy
      rw [← hpow]
      exact (Commute.pow_left (show Commute (s * l⁻¹) y from hc y hy) _).eq
    have h1 : (l⁻¹) ^ 2 ^ m = 1 := hZK _ hlm hlcen
    refine ⟨m, ?_⟩
    apply Subtype.ext
    show l ^ 2 ^ m = 1
    have : (l ^ 2 ^ m)⁻¹ = 1 := by rw [← inv_pow]; exact h1
    simpa using this
  have hSKW : N.SK ≤ W := fun k hk => ⟨hk.2, k, hk.1, fun x _ => rfl⟩
  have hWeq : W = N.SK := N.SK_sylow.eq_of_le hSKW hWK hW2
  obtain ⟨l, hlK, hl⟩ := hin
  have hlW : l ∈ W := ⟨hlK, s, hs', hl⟩
  rw [hWeq] at hlW
  have hcK : ∀ x ∈ N.K, (s * l⁻¹) * x = x * (s * l⁻¹) := by
    intro x hx
    calc s * l⁻¹ * x = s * (l⁻¹ * x * l) * l⁻¹ := by group
      _ = s * (s⁻¹ * x * s) * l⁻¹ := by rw [hl x hx]
      _ = x * (s * l⁻¹) := by group
  refine ⟨s * l⁻¹, ⟨N.S.mul_mem hs' (N.S.inv_mem (N.SK_le_S hlW)), ?_⟩, l, hlW, by group⟩
  rw [hK0]
  exact Subgroup.mem_centralizer_iff.mpr fun x hx => (hcK x hx).symm

theorem inner_mem_R_cover (h : Lv2513 N t zK) (F : K33Facts N.K) {r : G}
    (hr : r ∈ centSKz N.S N.K zK) (hin : Ch1.InducesInner r N.K) :
    ∃ i : Fin 2, ∃ c ∈ N.SC, r = c * (![1, zK] i) := by
  have hf := h.facts2511
  have hzKK := zK_mem_K N h F
  have hKz := F.inv zK hzKK (zK_ne_one N hf) (by rw [sq]; exact zK_mul_self N hf)
  rw [mem_centSKz_iff] at hr
  obtain ⟨c, hc, k, hk, rfl⟩ := inner_mem_SC_mul_SK N h F hr.1 hin
  have hkc : ∀ v ∈ threeCoreCent N.K zK, k * v = v * k := by
    intro v hv
    have h1 := hr.2 v hv
    have hvK : v ∈ N.K0 := N.K_le_K0 (threeCoreCent_le N.K zK hv)
    have h2 : v * c = c * v := Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer hc) v hvK
    have h3 : c * (v * k) = c * (k * v) := by
      calc c * (v * k) = (c * v) * k := by group
        _ = (v * c) * k := by rw [h2]
        _ = v * (c * k) := by group
        _ = (c * k) * v := h1
        _ = c * (k * v) := by group
    exact (mul_left_cancel h3).symm
  rcases hKz.centralizer k (N.SK_le_K hk) hkc with h1 | h1
  · exact ⟨0, c, hc, by simp [h1]⟩
  · exact ⟨1, c, hc, by simp [h1]⟩

theorem SC_sup_conjugate (h : Lv2513 N t zK) (F : K33Facts N.K) {x' : G}
    (hx'P : x' ∈ T ⊓ Subgroup.normalizer (N.S : Set G)) (hx'S : x' ∉ N.S) (hx'2 : x' ^ 2 ∈ N.S)
    (hx'c : ∀ v ∈ threeCoreCent N.K zK, x' * v = v * x') :
    N.SC ⊔ CFSG.conjugate N.SC x' ≤ centSKz N.S N.K zK ∧
      Nat.card ↥(N.SC ⊔ CFSG.conjugate N.SC x') = Nat.card N.SC * Nat.card N.SC ∧
      (∀ a ∈ N.SC, ∀ b ∈ CFSG.conjugate N.SC x', a * b = b * a) := by
  let N' : Notation25 hs :=
    { N with x := x', x_mem := hx'P, x_not_mem := hx'S, x_sq := hx'2 }
  have h255 : N.SC ⊓ CFSG.conjugate N.SC x' = ⊥ ∧ CFSG.conjugate N.SC x' ≤ N.S ∧
      ∀ a ∈ N.SC, ∀ b ∈ CFSG.conjugate N.SC x', a * b = b * a := lemma255 G T M hs N'
  obtain ⟨hinf, hle, hcomm⟩ := h255
  have hKH := H_le_normalizer_K N h F
  have hK0 : N.K0 = N.K := N.K0_eq hKH
  have hSCR : N.SC ≤ centSKz N.S N.K zK := by
    intro c hc
    rw [mem_centSKz_iff]
    refine ⟨N.SC_le_S hc, fun v hv => ?_⟩
    have hvK : v ∈ N.K0 := N.K_le_K0 (threeCoreCent_le N.K zK hv)
    exact Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer hc) v hvK
  have hconjR : CFSG.conjugate N.SC x' ≤ centSKz N.S N.K zK := by
    intro b hb
    rw [mem_centSKz_iff]
    refine ⟨hle hb, fun v hv => ?_⟩
    have hc : x' * b * x'⁻¹ ∈ N.SC := BenderBranch.mem_conjugate_iff.mp hb
    have hvK : v ∈ N.K0 := N.K_le_K0 (threeCoreCent_le N.K zK hv)
    have hcv : v * (x' * b * x'⁻¹) = (x' * b * x'⁻¹) * v :=
      Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer hc) v hvK
    have hxv : x' * v = v * x' := hx'c v hv
    have hxv' : x'⁻¹ * v = v * x'⁻¹ := by
      calc x'⁻¹ * v = x'⁻¹ * (v * x') * x'⁻¹ := by group
        _ = x'⁻¹ * (x' * v) * x'⁻¹ := by rw [hxv]
        _ = v * x'⁻¹ := by group
    have alg : ∀ c : G, v * c = c * v → v * (x'⁻¹ * c * x') = (x'⁻¹ * c * x') * v := by
      intro c hcv
      calc v * (x'⁻¹ * c * x') = (v * x'⁻¹) * c * x' := by group
        _ = (x'⁻¹ * v) * c * x' := by rw [← hxv']
        _ = x'⁻¹ * (v * c) * x' := by group
        _ = x'⁻¹ * (c * v) * x' := by rw [hcv]
        _ = x'⁻¹ * c * (v * x') := by group
        _ = x'⁻¹ * c * (x' * v) := by rw [← hxv]
        _ = (x'⁻¹ * c * x') * v := by group
    calc v * b = v * (x'⁻¹ * (x' * b * x'⁻¹) * x') := by group
      _ = (x'⁻¹ * (x' * b * x'⁻¹) * x') * v := alg _ hcv
      _ = b * v := by group
  refine ⟨sup_le hSCR hconjR, ?_, hcomm⟩
  rw [BenderBranch.card_sup_of_commute_of_inf_eq_bot hcomm hinf, BenderBranch.card_conjugate]

theorem comm_mem_centSKz (h : Lv2513 N t zK) (F : K33Facts N.K)
    (hKt : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N.K : Set G)) {e x' : G}
    (he : e ∈ N.S) (hx' : x' ∈ Subgroup.normalizer (N.S : Set G))
    (hx'c : ∀ v ∈ threeCoreCent N.K zK, x' * v = v * x') :
    e⁻¹ * (x'⁻¹ * e * x') ∈ centSKz N.S N.K zK := by
  rw [mem_centSKz_iff]
  have hxe : x'⁻¹ * e * x' ∈ N.S := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx') e).mp he
    simpa using this
  refine ⟨N.S.mul_mem (N.S.inv_mem he) hxe, fun v hv => ?_⟩
  have heN : e ∈ Subgroup.normalizer (threeCoreCent N.K zK : Set G) := by
    rw [← Kz_eq N h F hKt]
    exact mem_normalizer_Kz (Subgroup.le_normalizer he)
  have hv' : e * v * e⁻¹ ∈ threeCoreCent N.K zK := (Subgroup.mem_normalizer_iff.mp heN v).mp hv
  have hxv' : x' * (e * v * e⁻¹) = (e * v * e⁻¹) * x' := hx'c _ hv'
  have hxv'' : x'⁻¹ * (e * v * e⁻¹) = (e * v * e⁻¹) * x'⁻¹ := by
    calc x'⁻¹ * (e * v * e⁻¹) = x'⁻¹ * ((e * v * e⁻¹) * x') * x'⁻¹ := by group
      _ = x'⁻¹ * (x' * (e * v * e⁻¹)) * x'⁻¹ := by rw [← hxv']
      _ = (e * v * e⁻¹) * x'⁻¹ := by group
  have hxv : x' * v = v * x' := hx'c v hv
  calc v * (e⁻¹ * (x'⁻¹ * e * x')) = e⁻¹ * ((e * v * e⁻¹) * x'⁻¹) * e * x' := by group
    _ = e⁻¹ * (x'⁻¹ * (e * v * e⁻¹)) * e * x' := by rw [hxv'']
    _ = e⁻¹ * x'⁻¹ * e * (v * x') := by group
    _ = e⁻¹ * x'⁻¹ * e * (x' * v) := by rw [← hxv]
    _ = (e⁻¹ * (x'⁻¹ * e * x')) * v := by group

theorem SC_eq_zpowers (hf : Facts2511 N t zK) (hcard : Nat.card N.SC ≤ 2) :
    N.SC = Subgroup.zpowers t := by
  have hord : orderOf t = 2 := orderOf_eq_prime hf.t_sq hf.t_ne_one
  have hle : Subgroup.zpowers t ≤ N.SC := Subgroup.zpowers_le.mpr hf.t_mem
  symm
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hord]; exact hcard)

theorem exists_pair_E (h : Lv2513 N t zK) (F : K33Facts N.K)
    (hKt : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N.K : Set G)) :
    ∃ U HU E : Subgroup G, IsUStarPair M N.H U HU ∧ U ≤ N.S ∧
      HU = N.H ⊓ Subgroup.normalizer (E : Set G) ∧
      U = N.S ⊓ Subgroup.normalizer (E : Set G) ∧ E ≤ N.SK ∧ IsFourSubgroup E ∧ N.z ∈ E := by
  have hKH := H_le_normalizer_K N h F
  obtain ⟨U, HU, hpair, hUS⟩ := exists_ustarPair_le_S N
  obtain ⟨⟨E, hESK, hE4, hHU, hU, -, -, hEc⟩, -⟩ := (h.concl2512 hKH).1 U HU hpair hUS
  refine ⟨U, HU, E, hpair, hUS, hHU, hU, hESK, hE4, ?_⟩
  obtain ⟨hzz, -⟩ := z_eq_zK N h F hKt
  have hzK : N.z ∈ N.K := hzz ▸ zK_mem_K N h F
  have hzc : N.z ∈ Subgroup.centralizer (E : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun e he => N.comm_z_of_mem_S (N.SK_le_S (hESK he))
  have hmem : N.z ∈ N.K ⊓ Subgroup.centralizer (E : Set G) := ⟨hzK, hzc⟩
  rwa [← hEc] at hmem

end Config

end CFSG.QuasithinUnique.Unc25K1
