module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InSinger
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InClauses2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InPartII4

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem commute_of_sup {A B : Subgroup G} (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
  have hN : B ≤ Subgroup.normalizer (A : Set G) := le_normalizer_of_commute hAB
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hN).1 hx
  obtain ⟨a', ha', b', hb', rfl⟩ := (mem_sup_iff_of_le_normalizer hN).1 hy
  have e1 : a * a' = a' * a := hA a ha a' ha'
  have e2 : b * b' = b' * b := hB b hb b' hb'
  have e3 : a * b' = b' * a := hAB a ha b' hb'
  have e4 : a' * b = b * a' := hAB a' ha' b hb
  calc a * b * (a' * b') = a * (b * a') * b' := by group
    _ = a * (a' * b) * b' := by rw [e4]
    _ = (a * a') * (b * b') := by group
    _ = (a' * a) * (b' * b) := by rw [e1, e2]
    _ = a' * (a * b') * b := by group
    _ = a' * (b' * a) * b := by rw [e3]
    _ = a' * b' * (a * b) := by group

section Clauses4

variable (h : Lin2Cfg G T M H S L n D) (dat : Lin2Data T M H S L n)
include h dat

omit dat in
theorem Lin2Cfg.D_comm {a b : G} (ha : a ∈ D) (hb : b ∈ D) : a * b = b * a := by
  have := h.isCyclic_D
  exact congrArg Subtype.val ((IsCyclic.commGroup (α := D)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩)

omit dat in
theorem Lin2Cfg.conjR_D_comm {x : G} {a b : G} (ha : a ∈ conjR D x) (hb : b ∈ conjR D x) :
    a * b = b * a := by
  have h1 := h.D_comm (mem_conjR.1 ha) (mem_conjR.1 hb)
  have e1 : x * a * x⁻¹ * (x * b * x⁻¹) = x * (a * b) * x⁻¹ := by group
  have e2 : x * b * x⁻¹ * (x * a * x⁻¹) = x * (b * a) * x⁻¹ := by group
  rw [e1, e2] at h1
  have := mul_left_cancel (mul_right_cancel h1)
  exact this

theorem Lin2Data.D_inf_conjR_D_eq_bot (hZ : blockZ L ≠ ⊥) {x : G} (hx : x ∈ T) (hxS : x ∉ S) :
    D ⊓ conjR D x = ⊥ := by
  by_contra hne
  obtain ⟨d₁, hd₁⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hd₁1 : (d₁ : G) ≠ 1 := fun e => hd₁ (Subtype.ext e)
  obtain ⟨z, hz⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZ
  have hz1 : (z : G) ≠ 1 := fun e => hz (Subtype.ext e)
  have hzD₀ : (z : G) ∈ blockD S L := dat.Z_le_D₀ h z.2
  have hzR : (z : G) ∈ thompsonJ S := dat.D₀_le_R h hzD₀
  have hd₁D : (d₁ : G) ∈ D := d₁.2.1
  have hd₁E : (d₁ : G) ∈ conjR D x := d₁.2.2
  obtain ⟨δ, hδ, hδe⟩ := mem_conjR_iff'.1 hd₁E
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    apply hd₁1
    rw [hδe]
    simp
  have hcomm : (z : G) * d₁ = d₁ * z := dat.D₀_comm hzD₀ (h.D_le_L hd₁D)
  rw [hδe] at hcomm
  have hxR := dat.x_normalizer_R h hx
  have hxz : x * z * x⁻¹ ∈ thompsonJ S := (Subgroup.mem_normalizer_iff.1 hxR z).1 hzR
  have hc : δ * (x * z * x⁻¹) = (x * z * x⁻¹) * δ := by
    calc δ * (x * z * x⁻¹) = x * ((x⁻¹ * δ * x) * z) * x⁻¹ := by group
      _ = x * (z * (x⁻¹ * δ * x)) * x⁻¹ := by rw [← hcomm]
      _ = (x * z * x⁻¹) * δ := by group
  have hmem : x * z * x⁻¹ ∈ blockD S L := dat.centralizer_R h hδ hδ1 hxz hc
  have : (z : G) ∈ blockD S L ⊓ conjR (blockD S L) x := ⟨hzD₀, mem_conjR.2 hmem⟩
  rw [dat.D₀_inf x hx hxS, Subgroup.mem_bot] at this
  exact hz1 this

omit [Finite G] h dat in
theorem Lin2BPropsNA.toBProps {T S R D B : Subgroup G} (hNA : Lin2BPropsNA T S R D B)
    (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) : Lin2BProps T S R D B := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := hNA
  exact ⟨h1, h2, hab, h3, h4, h5, h6, h7, h8, h9, h10⟩

omit dat in
theorem Lin2Cfg.exists_mem_normalizer_not_mem_S {B : Subgroup G}
    (hNA : Lin2BPropsNA T S (thompsonJ S) D B) :
    ∃ x ∈ T, x ∈ Subgroup.normalizer (B : Set G) ∧ x ∉ S := by
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := hNA
  by_contra hcon
  push Not at hcon
  have : T ≤ S := by
    rw [← h8]
    exact sup_le (thompsonJ_le_self S) (fun t ht => hcon t ht.1 ht.2)
  exact h.S_ne_T (le_antisymm h.S_le_T this)

theorem Lin2Data.B_abelian_of_Z_ne_bot {B : Subgroup G} (hZ : blockZ L ≠ ⊥)
    (hNA : Lin2BPropsNA T S (thompsonJ S) D B) : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
  obtain ⟨x, hxT, hxN, hxS⟩ := h.exists_mem_normalizer_not_mem_S hNA
  obtain ⟨hDB, -, -, -, -, -, -, -, -, h10, h11⟩ := hNA
  have hx : x ∈ T ⊓ Subgroup.normalizer (B : Set G) := ⟨hxT, hxN⟩
  have hx' : x⁻¹ ∈ T ⊓ Subgroup.normalizer (B : Set G) :=
    ⟨T.inv_mem hxT, Subgroup.inv_mem _ hxN⟩
  have hxS' : x⁻¹ ∉ S := fun hh => hxS (by simpa using S.inv_mem hh)
  have hBeq := h10 x hx hxS
  have hEN := h11 x hx hxS
  have hEN' := h11 x⁻¹ hx' hxS'
  have hDN : D ≤ Subgroup.normalizer ((conjR D x : Subgroup G) : Set G) := by
    refine le_normalizer_of_conj_mem fun d hd e he => ?_
    rw [mem_conjR] at he ⊢
    have h1 : x * d * x⁻¹ ∈ conjR D x⁻¹ := by
      rw [mem_conjR]
      simpa [mul_assoc] using hd
    have h2 := (Subgroup.mem_normalizer_iff.1 (hEN' h1) (x * e * x⁻¹)).1 he
    have e1 : x * (d * e * d⁻¹) * x⁻¹ = (x * d * x⁻¹) * (x * e * x⁻¹) * (x * d * x⁻¹)⁻¹ := by
      group
    rw [e1]
    exact h2
  have hDE : D ⊓ conjR D x = ⊥ := dat.D_inf_conjR_D_eq_bot h hZ hx.1 hxS
  have hcomm : ∀ d ∈ D, ∀ e ∈ conjR D x, d * e = e * d := by
    intro d hd e he
    have h1 : e * d * e⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.1 (hEN he) d).1 hd
    have h2 : d * e⁻¹ * d⁻¹ ∈ conjR D x :=
      (Subgroup.mem_normalizer_iff.1 (hDN hd) e⁻¹).1 ((conjR D x).inv_mem he)
    have h3 : e * d * e⁻¹ * d⁻¹ ∈ D ⊓ conjR D x := by
      refine ⟨D.mul_mem h1 (D.inv_mem hd), ?_⟩
      have : e * d * e⁻¹ * d⁻¹ = e * (d * e⁻¹ * d⁻¹) := by group
      rw [this]
      exact (conjR D x).mul_mem he h2
    rw [hDE, Subgroup.mem_bot] at h3
    calc d * e = (e * d * e⁻¹) * e := by rw [mul_inv_eq_one.1 h3]
      _ = e * d := by group
  intro a ha b hb
  rw [hBeq] at ha hb
  exact commute_of_sup (fun a ha a' ha' => h.D_comm ha ha')
    (fun b hb b' hb' => h.conjR_D_comm hb hb') hcomm a ha b hb

theorem Lin2Data.card_center_R_of_Z_bot (hZ : blockZ L = ⊥) :
    Nat.card (centerOf (thompsonJ S)) = 2 ^ n := by
  obtain ⟨x, hx, hxS⟩ := h.exists_mem_T_not_mem_S
  obtain ⟨W, hWeq, -, hcard, -⟩ := dat.exists_W h hx hxS
  rw [← dat.U_inf_conjU_eq_center h hx hxS, ← hWeq]
  have hU := lin2_card_U h.lin2
  rw [hZ, Subgroup.card_bot, mul_one] at hU
  have h2n : 0 < 2 ^ n := by positivity
  apply Nat.eq_of_mul_eq_mul_right h2n
  rw [hcard, hU]
  ring

theorem Lin2Data.center_R_regular_of_Z_bot (hZ : blockZ L = ⊥) :
    ActsRegularlyOn D (nonIdentity (centerOf (thompsonJ S))) := by
  have hD₀ : blockD S L = ⊥ := dat.D₀_eq_bot_of_Z_bot h hZ
  have hY : ∀ a ∈ D, ∀ y ∈ centerOf (thompsonJ S), a⁻¹ * y * a ∈ centerOf (thompsonJ S) := by
    intro a ha y hy
    have hn := Subgroup.inv_mem _ (dat.D_le_normalizer_R h ha)
    have h1 : y ∈ conjR (centerOf (thompsonJ S)) a⁻¹ := by
      rw [centerOf_normalized hn]
      exact hy
    have := mem_conjR.1 h1
    simpa using this
  have hfree : ∀ a ∈ D, a ≠ 1 → ∀ y ∈ centerOf (thompsonJ S), a⁻¹ * y * a = y → y = 1 := by
    intro a ha ha1 y hy hay
    have hyR : y ∈ thompsonJ S := hy.1
    have hc : a * y = y * a := by
      have h1 : y * a = a * y := by
        calc y * a = a * (a⁻¹ * y * a) := by group
          _ = a * y := by rw [hay]
      exact h1.symm
    have := dat.centralizer_R h ha ha1 hyR hc
    rw [hD₀, Subgroup.mem_bot] at this
    exact this
  have hcard : Nat.card (centerOf (thompsonJ S)) = Nat.card D + 1 := by
    rw [dat.card_center_R_of_Z_bot h hZ, h.card_D]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  refine ⟨?_, ?_, ?_⟩
  · rintro b hb z ⟨hz, hz1⟩
    refine ⟨hY b hb z hz, fun e => hz1 ?_⟩
    have := congrArg (fun w => b * w * b⁻¹) e
    simpa [mul_assoc] using this
  · rintro z ⟨hz, hz1⟩ z' ⟨hz', hz1'⟩
    exact transitive_of_free_of_card hY hfree hcard hz hz1 hz' hz1'
  · rintro z ⟨hz, hz1⟩ b hb hbz
    by_contra hb1
    exact hz1 (hfree b hb hb1 z hz hbz)

theorem Lin2Data.le_sup_centralizer_of_abelian (hZ : blockZ L = ⊥) {B : Subgroup G} (hDB : D ≤ B)
    (hBN : B ≤ Subgroup.normalizer (thompsonJ S : Set G))
    (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    B ≤ D ⊔ Subgroup.centralizer (centerOf (thompsonJ S) : Set G) := by
  have hreg := dat.center_R_regular_of_Z_bot h hZ
  have hYne : centerOf (thompsonJ S) ≠ ⊥ := by
    intro hbot
    have := dat.card_center_R_of_Z_bot h hZ
    rw [hbot, Subgroup.card_bot] at this
    have h4 : 4 ≤ 2 ^ n := h.four_le_two_pow
    omega
  obtain ⟨y₀, hy₀⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hYne
  have hy₀1 : (y₀ : G) ≠ 1 := fun e => hy₀ (Subtype.ext e)
  have hy₀Δ : (y₀ : G) ∈ nonIdentity (centerOf (thompsonJ S)) := ⟨y₀.2, hy₀1⟩
  intro b hb
  have hbn : b ∈ Subgroup.normalizer (thompsonJ S : Set G) := hBN hb
  have hbY : b⁻¹ * y₀ * b ∈ centerOf (thompsonJ S) := by
    have hn := Subgroup.inv_mem _ hbn
    have h1 : (y₀ : G) ∈ conjR (centerOf (thompsonJ S)) b⁻¹ := by
      rw [centerOf_normalized hn]
      exact y₀.2
    have := mem_conjR.1 h1
    simpa using this
  have hb1 : b⁻¹ * y₀ * b ≠ 1 := by
    intro e
    apply hy₀1
    have := congrArg (fun w => b * w * b⁻¹) e
    simpa [mul_assoc] using this
  obtain ⟨d₁, hd₁, hd₁e⟩ := hreg.2.1 _ hy₀Δ _ ⟨hbY, hb1⟩
  have hcB : b * d₁⁻¹ ∈ B := B.mul_mem hb (B.inv_mem (hDB hd₁))
  have hc0 : b * d₁⁻¹ * y₀ * (b * d₁⁻¹)⁻¹ = y₀ := by
    calc b * d₁⁻¹ * y₀ * (b * d₁⁻¹)⁻¹ = b * (d₁⁻¹ * y₀ * d₁) * b⁻¹ := by group
      _ = b * (b⁻¹ * y₀ * b) * b⁻¹ := by rw [hd₁e]
      _ = y₀ := by group
  have hcC : b * d₁⁻¹ ∈ Subgroup.centralizer (centerOf (thompsonJ S) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1]
      simp
    · obtain ⟨d, hd, hdy⟩ := hreg.2.1 _ hy₀Δ _ ⟨hy, hy1⟩
      have e1 : b * d₁⁻¹ * d⁻¹ = d⁻¹ * (b * d₁⁻¹) := hab _ hcB d⁻¹ (B.inv_mem (hDB hd))
      have e2 : (b * d₁⁻¹)⁻¹ * d = d * (b * d₁⁻¹)⁻¹ := hab _ (B.inv_mem hcB) d (hDB hd)
      have hconj : b * d₁⁻¹ * y * (b * d₁⁻¹)⁻¹ = y := by
        rw [← hdy]
        calc b * d₁⁻¹ * (d⁻¹ * y₀ * d) * (b * d₁⁻¹)⁻¹
            = (b * d₁⁻¹ * d⁻¹) * y₀ * (d * (b * d₁⁻¹)⁻¹) := by group
          _ = (d⁻¹ * (b * d₁⁻¹)) * y₀ * ((b * d₁⁻¹)⁻¹ * d) := by rw [e1, ← e2]
          _ = d⁻¹ * (b * d₁⁻¹ * y₀ * (b * d₁⁻¹)⁻¹) * d := by group
          _ = d⁻¹ * y₀ * d := by rw [hc0]
      calc y * (b * d₁⁻¹) = (b * d₁⁻¹ * y * (b * d₁⁻¹)⁻¹) * (b * d₁⁻¹) := by rw [hconj]
        _ = (b * d₁⁻¹) * y := by group
  have hb' : b = (b * d₁⁻¹) * d₁ := by group
  rw [hb']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcC) (Subgroup.mem_sup_left hd₁)

theorem Lin2Data.B_abelian_of_Z_bot {B : Subgroup G} (hZ : blockZ L = ⊥)
    (hNA : Lin2BPropsNA T S (thompsonJ S) D B) : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
  obtain ⟨x, hxT, hxN, hxS⟩ := h.exists_mem_normalizer_not_mem_S hNA
  obtain ⟨hDB, -, -, -, hBN, -, -, -, -, h10, h11⟩ := hNA
  have hx : x ∈ T ⊓ Subgroup.normalizer (B : Set G) := ⟨hxT, hxN⟩
  have hBeq := h10 x hx hxS
  have hEN := h11 x hx hxS
  have hBD : B ≤ Subgroup.normalizer (D : Set G) := by
    rw [hBeq]
    exact sup_le Subgroup.le_normalizer hEN
  have hxR := dat.x_normalizer_R h hxT
  have hZB : B ≤ Subgroup.normalizer (centerOf (thompsonJ S) : Set G) := by
    intro b hb
    rw [← conjR_eq_self_iff]
    exact centerOf_normalized (hBN hb)
  have hZel : IsElemAbelian 2 (centerOf (thompsonJ S)) := by
    rw [← dat.U_inf_conjU_eq_center h hxT hxS]
    exact IsElemAbelian.mono inf_le_left (dat.U_elem h)
  have hZcard := dat.card_center_R_of_Z_bot h hZ
  have hZne : centerOf (thompsonJ S) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZcard
    have h4 : 4 ≤ 2 ^ n := h.four_le_two_pow
    omega
  have hDreg := dat.center_R_regular_of_Z_bot h hZ
  have hEfree : ∀ y ∈ conjR D x, (∀ z ∈ centerOf (thompsonJ S), y * z = z * y) → y = 1 := by
    intro y hy hyc
    obtain ⟨d, hd, rfl⟩ := mem_conjR_iff'.1 hy
    have hdc : ∀ z ∈ centerOf (thompsonJ S), d * z = z * d := by
      intro z hz
      have hz' : x⁻¹ * z * x ∈ centerOf (thompsonJ S) := by
        have h1 : z ∈ conjR (centerOf (thompsonJ S)) x⁻¹ := by
          rw [centerOf_normalized (Subgroup.inv_mem _ hxR)]
          exact hz
        simpa using mem_conjR.1 h1
      have h2 := hyc _ hz'
      calc d * z = x * (x⁻¹ * d * x * (x⁻¹ * z * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * z * x) * (x⁻¹ * d * x)) * x⁻¹ := by rw [h2]
        _ = z * d := by group
    rw [eq_one_of_centralizes_of_acts_regularly hZne hDreg hd hdc]
    group
  have hEB : conjR D x ≤ B := by
    rw [hBeq]
    exact le_sup_right
  have hcomm := commute_of_singer (Z := centerOf (thompsonJ S)) (D := D) (E := conjR D x)
    (B := B) (e := n) (by have := h.one_lt; omega) hZel hZcard hZB hDB hEB
    (fun b hb d hd => (Subgroup.mem_normalizer_iff.1 (hBD hb) d).1 hd)
    (fun a ha b hb => h.D_comm ha hb) (fun a ha b hb => h.conjR_D_comm ha hb) hDreg h.card_D
    hEfree (by rw [card_conjR]; exact h.card_D)
  intro a ha b hb
  rw [hBeq] at ha hb
  exact commute_of_sup (fun a ha a' ha' => h.D_comm ha ha')
    (fun b hb b' hb' => h.conjR_D_comm hb hb') hcomm a ha b hb

theorem Lin2Data.exists_B : ∃ B : Subgroup G, Lin2BProps T S (thompsonJ S) D B := by
  obtain ⟨B, hNA⟩ := dat.exists_BNA h
  refine ⟨B, hNA.toBProps ?_⟩
  by_cases hZ : blockZ L = ⊥
  · exact dat.B_abelian_of_Z_bot h hZ hNA
  · exact dat.B_abelian_of_Z_ne_bot h hZ hNA

theorem Lin2Data.clause6 {B : Subgroup G} (hB : Lin2BProps T S (thompsonJ S) D B) :
    (centerOf L ≠ ⊥ → ∀ x ∈ T ⊓ Subgroup.normalizer (B : Set G), x ∉ S →
        B = D ⊔ conjR D x ∧ D ⊓ conjR D x = ⊥) ∧
    (centerOf L = ⊥ → B ≤ D ⊔ Subgroup.centralizer (centerOf (thompsonJ S) : Set G) ∧
        ActsRegularlyOn D (nonIdentity (centerOf (thompsonJ S)))) := by
  obtain ⟨hDB, -, hab, -, -, hBN, -, -, -, -, h11⟩ := hB
  have hZc : blockZ L = centerOf L := blockZ_eq_centerOf h.charTwo_L dat.pCore_eq
  refine ⟨fun hZ x hx hxS => ⟨h11 x hx hxS, ?_⟩, fun hZ => ?_⟩
  · refine dat.D_inf_conjR_D_eq_bot h ?_ hx.1 hxS
    rw [hZc]
    exact hZ
  · have hZ' : blockZ L = ⊥ := by rw [hZc]; exact hZ
    exact ⟨dat.le_sup_centralizer_of_abelian h hZ' hDB hBN hab,
      dat.center_R_regular_of_Z_bot h hZ'⟩

end Clauses4

end CFSG.QuasithinUnique.Lin2
