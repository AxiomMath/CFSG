module

public import CFSG.CGT.PushingUpLit.A78S4.Base

public section

namespace CFSG.CGT.PushingUpLit.A78S4

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.CGT.PushingUpLit.A78L3
open CFSG.ABGLocalTools
open Matrix
open scoped commutatorElement

namespace S4Pair

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ T : Subgroup G} {e : ℕ}
  (P : S4Pair G L₁ L₂ V W Z Z₂ T e) (hZ : Z ≠ ⊥)

include P hZ

theorem utype_symm {u : G} (hu : UType V W Z Z₂ u) : UType W V Z₂ Z u :=
  ⟨by rw [inf_comm]; exact hu.1, hu.2.2, hu.2.1⟩

theorem utype_of_decomp {z z₂ : G} (hz : z ∈ Z) (hz₂ : z₂ ∈ Z₂) (hz1 : z ≠ 1) (hz₂1 : z₂ ≠ 1) :
    UType V W Z Z₂ (z * z₂) := by
  refine ⟨mul_mem (P.side₁.Z_le_N hz) (P.Z₂_le_N hz₂), fun h1 => hz₂1 ?_, fun h1 => hz1 ?_⟩
  · have h2 : z₂ ∈ Z ⊓ Z₂ := Subgroup.mem_inf.2 ⟨by simpa using mul_mem (inv_mem hz) h1, hz₂⟩
    rw [P.inf_Z] at h2
    exact h2
  · have h2 : z ∈ Z ⊓ Z₂ := Subgroup.mem_inf.2 ⟨hz, by simpa using mul_mem h1 (inv_mem hz₂)⟩
    rw [P.inf_Z] at h2
    exact h2

theorem decomp_of_utype {u : G} (hu : UType V W Z Z₂ u) :
    ∃ z ∈ Z, ∃ z₂ ∈ Z₂, z ≠ 1 ∧ z₂ ≠ 1 ∧ z * z₂ = u := by
  obtain ⟨z, hz, z₂, hz₂, rfl⟩ := P.exists_decomp hZ hu.1
  refine ⟨z, hz, z₂, hz₂, fun h1 => hu.2.2 ?_, fun h1 => hu.2.1 ?_, rfl⟩
  · rw [h1, one_mul]; exact hz₂
  · rw [h1, mul_one]; exact hz

theorem exists_torus₁ {z₂ z₂' : G} (hz₂ : z₂ ∈ Z₂) (hz₂1 : z₂ ≠ 1) (hz₂' : z₂' ∈ Z₂)
    (hz₂'1 : z₂' ≠ 1) :
    ∃ x ∈ L₁, (∀ j ∈ V ⊔ W, x * j * x⁻¹ ∈ V ⊔ W) ∧ x * z₂ * x⁻¹ = z₂' := by
  obtain ⟨D⟩ := P.side₁.nat
  obtain ⟨fr⟩ := P.side₁.exists_frame D
  have hZ₂ := P.Z₂_ne_bot hZ
  have hc0 : ∀ y ∈ Z₂, y ≠ 1 → fr.c y ≠ 0 := by
    intro y hy hy1 h0
    apply hy1
    have h1 : fr.c y = fr.c 1 := by rw [h0, fr.c_one]
    exact P.symm.zc_inj fr hy Z₂.one_mem h1
  have ht : fr.c z₂' / fr.c z₂ ≠ 0 := div_ne_zero (hc0 z₂' hz₂' hz₂'1) (hc0 z₂ hz₂ hz₂1)
  obtain ⟨x, hxL, hxJ, hxW, -, hxN⟩ := fr.torus ht
  refine ⟨x, hxL, hxJ, P.symm.zc_inj fr (P.conj_Z₂ (mem_normalizer_of_conj_le hxW) hz₂) hz₂' ?_⟩
  rw [(hxN z₂ (P.Z₂_le_N hz₂)).2]
  field_simp [hc0 z₂ hz₂ hz₂1]

theorem u_conj {u u' : G} (hu : UType V W Z Z₂ u) (hu' : UType V W Z Z₂ u') :
    ∃ n ∈ Subgroup.normalizer ((V ⊔ W : Subgroup G) : Set G), n * u * n⁻¹ = u' := by
  obtain ⟨z, hz, z₂, hz₂, hz1, hz₂1, rfl⟩ := P.decomp_of_utype hZ hu
  obtain ⟨z', hz', z₂', hz₂', hz'1, hz₂'1, rfl⟩ := P.decomp_of_utype hZ hu'
  obtain ⟨x, hxL, hxJ, hxz⟩ := P.exists_torus₁ hZ hz₂ hz₂1 hz₂' hz₂'1
  obtain ⟨y, hyL, hyJ, hyz⟩ := P.symm.exists_torus₁ (P.Z₂_ne_bot hZ) hz hz1 hz' hz'1
  have hxzc : x * z * x⁻¹ = z := by
    rw [Subgroup.mem_centralizer_iff.1 (P.side₁.Z_cent hz) x hxL]
    group
  have hyzc : y * z₂' * y⁻¹ = z₂' := by
    rw [Subgroup.mem_centralizer_iff.1 (P.side₂.Z_cent hz₂') y hyL]
    group
  have hyJ' : ∀ j ∈ V ⊔ W, y * j * y⁻¹ ∈ V ⊔ W := fun j hj => by
    have := hyJ j (by rw [sup_comm]; exact hj)
    rwa [sup_comm] at this
  refine ⟨y * x, mul_mem (mem_normalizer_of_conj_le hyJ') (mem_normalizer_of_conj_le hxJ), ?_⟩
  calc y * x * (z * z₂) * (y * x)⁻¹ = y * ((x * z * x⁻¹) * (x * z₂ * x⁻¹)) * y⁻¹ := by group
    _ = (y * z * y⁻¹) * (y * z₂' * y⁻¹) := by rw [hxzc, hxz]; group
    _ = z' * z₂' := by rw [hyz, hyzc]

section Sylow

variable (hsyl₁ : IsSylowOf 2 T (Subgroup.normalizer (V : Set G)))
  {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hTS : T ≤ S) (hsw : ∃ s ∈ S, s ∉ T)

include hsyl₁ hS hTS hsw

theorem exists_central_u : ∃ u₀ : G, UType V W Z Z₂ u₀ ∧ ∀ x ∈ S, x * u₀ = u₀ * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSp : IsPGroup 2 S := hS.isPGroup
  have hN := P.le_normalizer_T hZ hsyl₁ hTS hSp
  obtain ⟨s, hs, hsT⟩ := hsw
  have hswap := P.swap_of_mem_R hZ hsyl₁ hTS hSp hs (hN s hs) hsT
  have hswZ := P.swap_Z hZ hswap.1 hswap.2
  have hZel : ElemAb2 Z := fun x hx y hy =>
    ⟨(P.side₁.jst.abelian_V x (P.side₁.Z_le_V hx) y (P.side₁.Z_le_V hy)).eq,
      P.side₁.jst.sq_V x (P.side₁.Z_le_V hx)⟩
  obtain ⟨z₀, hz₀, hz₀1, hz₀T⟩ := exists_fixed_ne_one P.side₁.pT hZel hZ
    (fun t ht => cj_eq_of_mem_normalizer_set (P.side₁.T_le_Z ht))
  have hsz : s * z₀ * s⁻¹ ∈ Z₂ := hswZ.1 ▸ mul_mem_cj s hz₀
  have hsz1 : s * z₀ * s⁻¹ ≠ 1 := fun h1 => hz₀1 (by
    have : z₀ = s⁻¹ * (s * z₀ * s⁻¹) * s := by group
    rw [this, h1]; group)
  refine ⟨z₀ * (s * z₀ * s⁻¹), P.utype_of_decomp hZ hz₀ hsz hz₀1 hsz1, ?_⟩
  have hTu : ∀ t ∈ T, t * (z₀ * (s * z₀ * s⁻¹)) * t⁻¹ = z₀ * (s * z₀ * s⁻¹) := by
    intro t ht
    have hst : s⁻¹ * t * s ∈ T := by
      simpa using hN s⁻¹ (inv_mem hs) t ht
    have h1 : t * (s * z₀ * s⁻¹) * t⁻¹ = s * z₀ * s⁻¹ := by
      calc t * (s * z₀ * s⁻¹) * t⁻¹ = s * ((s⁻¹ * t * s) * z₀ * (s⁻¹ * t * s)⁻¹) * s⁻¹ := by
            group
        _ = s * z₀ * s⁻¹ := by rw [hz₀T _ hst]
    calc t * (z₀ * (s * z₀ * s⁻¹)) * t⁻¹ = (t * z₀ * t⁻¹) * (t * (s * z₀ * s⁻¹) * t⁻¹) := by
          group
      _ = z₀ * (s * z₀ * s⁻¹) := by rw [hz₀T t ht, h1]
  have hss : s * s ∈ T := P.mul_mem_T_of_R hZ hsyl₁ hTS hSp hs (hN s hs) hsT hs (hN s hs) hsT
  have hsu : s * (z₀ * (s * z₀ * s⁻¹)) * s⁻¹ = z₀ * (s * z₀ * s⁻¹) := by
    have h1 : s * (s * z₀ * s⁻¹) * s⁻¹ = z₀ := by
      calc s * (s * z₀ * s⁻¹) * s⁻¹ = (s * s) * z₀ * (s * s)⁻¹ := by group
        _ = z₀ := hz₀T _ hss
    calc s * (z₀ * (s * z₀ * s⁻¹)) * s⁻¹ = (s * z₀ * s⁻¹) * (s * (s * z₀ * s⁻¹) * s⁻¹) := by
          group
      _ = (s * z₀ * s⁻¹) * z₀ := by rw [h1]
      _ = z₀ * (s * z₀ * s⁻¹) := P.commute_N (P.Z₂_le_N hsz) (P.side₁.Z_le_N hz₀)
  intro x hx
  have hconj : x * (z₀ * (s * z₀ * s⁻¹)) * x⁻¹ = z₀ * (s * z₀ * s⁻¹) := by
    by_cases hxT : x ∈ T
    · exact hTu x hxT
    · have hsx : s⁻¹ * x ∈ T := by
        have h1 := P.mul_mem_T_of_R hZ hsyl₁ hTS hSp (inv_mem hs) (hN _ (inv_mem hs))
          (fun h => hsT (by simpa using inv_mem h)) hx (hN x hx) hxT
        exact h1
      calc x * (z₀ * (s * z₀ * s⁻¹)) * x⁻¹ =
            s * ((s⁻¹ * x) * (z₀ * (s * z₀ * s⁻¹)) * (s⁻¹ * x)⁻¹) * s⁻¹ := by group
        _ = z₀ * (s * z₀ * s⁻¹) := by rw [hTu _ hsx, hsu]
  calc x * (z₀ * (s * z₀ * s⁻¹)) = x * (z₀ * (s * z₀ * s⁻¹)) * x⁻¹ * x := by group
    _ = z₀ * (s * z₀ * s⁻¹) * x := by rw [hconj]

theorem u_not_conj (hsyl₂ : IsSylowOf 2 T (Subgroup.normalizer (W : Set G)))
    (hcent₁ : ∀ z ∈ Z, z ≠ 1 →
      Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hcent₂ : ∀ z ∈ Z₂, z ≠ 1 →
      Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (W : Set G)) :
    ∀ u z : G, UType V W Z Z₂ u → (z ∈ Z ∨ z ∈ Z₂) → z ≠ 1 → ∀ g : G, g⁻¹ * u * g ≠ z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro u z hu hz hz1 g hg
  obtain ⟨u₀, hu₀, hu₀S⟩ := P.exists_central_u hZ hsyl₁ hS hTS hsw
  obtain ⟨n, -, hn⟩ := P.u_conj hZ hu₀ hu
  set h := n⁻¹ * g with hh
  have hzu : z = h⁻¹ * u₀ * h := by rw [← hg, hh, ← hn]; group
  have hSC : cj h⁻¹ S ≤ Subgroup.centralizer ({z} : Set G) := by
    intro y hy
    rw [mem_cj_iff, inv_inv] at hy
    have h1 := hu₀S _ hy
    rw [Subgroup.mem_centralizer_singleton_iff, hzu]
    have e1 : y = h⁻¹ * (h * y * h⁻¹) * h := by group
    rw [e1]
    calc h⁻¹ * (h * y * h⁻¹) * h * (h⁻¹ * u₀ * h) = h⁻¹ * ((h * y * h⁻¹) * u₀) * h := by group
      _ = h⁻¹ * (u₀ * (h * y * h⁻¹)) * h := by rw [h1]
      _ = h⁻¹ * u₀ * h * (h⁻¹ * (h * y * h⁻¹) * h) := by group
  have hcS : IsPGroup 2 (cj h⁻¹ S) :=
    hS.isPGroup.of_equiv (MulEquiv.subgroupMap (MulAut.conj h⁻¹) S)
  have hle : Nat.card S ≤ Nat.card T := by
    rcases hz with hzZ | hzZ₂
    · obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hsyl₁ (hSC.trans (hcent₁ z hzZ hz1)) hcS
      have := Subgroup.card_le_of_le hk
      rwa [card_cj, card_cj] at this
    · obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hsyl₂ (hSC.trans (hcent₂ z hzZ₂ hz1)) hcS
      have := Subgroup.card_le_of_le hk
      rwa [card_cj, card_cj] at this
  obtain ⟨s, hs, hsT⟩ := hsw
  have hlt : T < S := lt_of_le_of_ne hTS fun h => hsT (h ▸ hs)
  have := Subgroup.card_lt_of_lt hlt
  omega

end Sylow

theorem inv_class_V {x : G} (hx : x ∈ V) (hx1 : x ≠ 1) :
    ∃ g : G, g⁻¹ * x * g ∈ Z ∨ g⁻¹ * x * g ∈ Z₂ ∨ UType V W Z Z₂ (g⁻¹ * x * g) := by
  by_cases hxZ : x ∈ Z
  · exact ⟨1, Or.inl (by simpa using hxZ)⟩
  obtain ⟨D⟩ := P.side₁.nat
  obtain ⟨fr⟩ := P.side₁.exists_frame D
  obtain ⟨l, hl, hlx⟩ := D.exists_conj hx hxZ fr.hn₀.1 fr.hn₀Z
  have hlxV : l * x * l⁻¹ ∈ V := D.norm l hl x hx
  have hlxN : l * x * l⁻¹ ∈ V ⊓ W := by
    have h1 := (D.κ_eq_iff hlxV fr.hn₀.1).1 hlx
    have e1 : l * x * l⁻¹ = (l * x * l⁻¹ * fr.n₀⁻¹) * fr.n₀ := by group
    rw [e1]
    exact mul_mem (P.side₁.Z_le_N h1) fr.hn₀
  have hlxZ : l * x * l⁻¹ ∉ Z := fun h1 => hxZ (by
    have h2 := P.side₁.T_le_Z
    have : x = l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ := by group
    rw [this]
    exact conj_mem_of_mem_normalizer (D.le_normalizer_K (inv_mem hl)) h1)
  obtain ⟨z, hz, z₂, hz₂, hdec⟩ := P.exists_decomp hZ hlxN
  have hz₂1 : z₂ ≠ 1 := fun h1 => hlxZ (by rw [← hdec, h1, mul_one]; exact hz)
  refine ⟨l⁻¹, ?_⟩
  rw [inv_inv]
  by_cases hz1 : z = 1
  · exact Or.inr (Or.inl (by rw [← hdec, hz1, one_mul]; exact hz₂))
  · exact Or.inr (Or.inr (by rw [← hdec]; exact P.utype_of_decomp hZ hz hz₂ hz1 hz₂1))

theorem inv_class {x : G} (hx : x ∈ V ⊔ W) (hxx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ g : G, g⁻¹ * x * g ∈ Z ∨ g⁻¹ * x * g ∈ Z₂ ∨ UType V W Z Z₂ (g⁻¹ * x * g) := by
  rcases P.side₁.jst.involution_mem hx hxx with hV | hW
  · exact P.inv_class_V hZ hV hx1
  · obtain ⟨g, hg⟩ := P.symm.inv_class_V (P.Z₂_ne_bot hZ) hW hx1
    refine ⟨g, ?_⟩
    rcases hg with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (P.symm.utype_symm (P.Z₂_ne_bot hZ) h))

theorem sup_eq_of_inf_eq_bot {A : Subgroup G} (hAV : A ≤ V) (hA : Nat.card A = 2 ^ e)
    (hNA : (V ⊓ W) ⊓ A = ⊥) : (V ⊓ W) ⊔ A = V := by
  refine Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left hAV) ?_
  let g : ↥(V ⊓ W) × ↥A → ↥((V ⊓ W) ⊔ A) := fun p =>
    ⟨p.1 * p.2, mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hg : Function.Injective g := by
    rintro ⟨n, a⟩ ⟨n', a'⟩ hnn
    have h1 : (n : G) * a = n' * a' := congrArg Subtype.val hnn
    have h2 : (n' : G)⁻¹ * n = a' * (a : G)⁻¹ := by
      calc (n' : G)⁻¹ * n = (n' : G)⁻¹ * (n * a) * (a : G)⁻¹ := by group
        _ = (n' : G)⁻¹ * (n' * a') * (a : G)⁻¹ := by rw [h1]
        _ = a' * (a : G)⁻¹ := by group
    have h3 : (n' : G)⁻¹ * n ∈ (V ⊓ W) ⊓ A :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem n'.2) n.2, by rw [h2]; exact mul_mem a'.2 (inv_mem a.2)⟩
    rw [hNA, Subgroup.mem_bot] at h3
    have hn : (n : G) = n' := by
      have := congrArg (fun y => (n' : G) * y) h3
      simpa using this
    have ha : (a : G) = a' := by
      rw [hn] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext hn) (Subtype.ext ha)
  have h1 := Nat.card_le_card_of_injective g hg
  rw [Nat.card_prod, P.card_N hZ, hA, ← pow_add] at h1
  rw [P.card_V3 hZ]
  calc 2 ^ (3 * e) = 2 ^ (2 * e + e) := by ring_nf
    _ ≤ _ := h1

theorem conj_in_V {s : G} (hsZ : cj s Z = Z₂ ∧ cj s Z₂ = Z)
    (hti₁ : ∀ g : G, Z ⊓ cj g Z ≠ ⊥ → cj g Z = Z)
    (hti₂ : ∀ g : G, Z₂ ⊓ cj g Z₂ ≠ ⊥ → cj g Z₂ = Z₂)
    (hnot : ∀ u z : G, UType V W Z Z₂ u → (z ∈ Z ∨ z ∈ Z₂) → z ≠ 1 → ∀ g : G, g⁻¹ * u * g ≠ z)
    (A : Subgroup G) (hA : ∃ g : G, A = cj g Z ∨ A = cj g Z₂) (hAV : A ≤ V) :
    (A = Z ∨ A = Z₂) ∨ ((V ⊓ W) ⊔ A = V ∧ (V ⊓ W) ⊓ A = ⊥) := by
  obtain ⟨g, hg⟩ := hA
  have hAZ : A = cj g Z ∨ A = cj (g * s) Z := by
    rcases hg with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h, ← cj_cj, hsZ.1])
  have hAZ₂ : A = cj g Z₂ ∨ A = cj (g * s) Z₂ := by
    rcases hg with h | h
    · exact Or.inr (by rw [h, ← cj_cj, hsZ.2])
    · exact Or.inl h
  have hcardA : Nat.card A = 2 ^ e := by
    rcases hg with h | h
    · rw [h, card_cj, P.card_Z hZ]
    · rw [h, card_cj, P.card_Z₂ hZ]
  by_cases hNA : (V ⊓ W) ⊓ A = ⊥
  · exact Or.inr ⟨P.sup_eq_of_inf_eq_bot hZ hAV hcardA hNA, hNA⟩
  left
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ (V ⊓ W) ⊓ A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hNA ((Subgroup.eq_bot_iff_forall _).2 hcon)
  have hconj : ∃ k : G, (k⁻¹ * a * k ∈ Z ∨ k⁻¹ * a * k ∈ Z₂) ∧ k⁻¹ * a * k ≠ 1 := by
    rcases hg with h | h
    · refine ⟨g, Or.inl ?_, ?_⟩
      · have := (Subgroup.mem_inf.1 ha).2
        rw [h, mem_cj_iff] at this
        exact this
      · intro h1; apply ha1
        have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
        rw [this, h1]; group
    · refine ⟨g, Or.inr ?_, ?_⟩
      · have := (Subgroup.mem_inf.1 ha).2
        rw [h, mem_cj_iff] at this
        exact this
      · intro h1; apply ha1
        have : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
        rw [this, h1]; group
  obtain ⟨k, hk, hk1⟩ := hconj
  obtain ⟨z, hz, z₂, hz₂, hdec⟩ := P.exists_decomp hZ ha.1
  by_cases hz1 : z = 1
  ·
    have haZ₂ : a ∈ Z₂ := by rw [← hdec, hz1, one_mul]; exact hz₂
    right
    rcases hAZ₂ with h | h
    · rw [h]
      refine hti₂ g fun hbot => ha1 ?_
      have : a ∈ Z₂ ⊓ cj g Z₂ := Subgroup.mem_inf.2 ⟨haZ₂, h ▸ (Subgroup.mem_inf.1 ha).2⟩
      rw [hbot] at this
      exact this
    · rw [h]
      refine hti₂ (g * s) fun hbot => ha1 ?_
      have : a ∈ Z₂ ⊓ cj (g * s) Z₂ := Subgroup.mem_inf.2 ⟨haZ₂, h ▸ (Subgroup.mem_inf.1 ha).2⟩
      rw [hbot] at this
      exact this
  by_cases hz₂1 : z₂ = 1
  ·
    have haZ : a ∈ Z := by rw [← hdec, hz₂1, mul_one]; exact hz
    left
    rcases hAZ with h | h
    · rw [h]
      refine hti₁ g fun hbot => ha1 ?_
      have : a ∈ Z ⊓ cj g Z := Subgroup.mem_inf.2 ⟨haZ, h ▸ (Subgroup.mem_inf.1 ha).2⟩
      rw [hbot] at this
      exact this
    · rw [h]
      refine hti₁ (g * s) fun hbot => ha1 ?_
      have : a ∈ Z ⊓ cj (g * s) Z := Subgroup.mem_inf.2 ⟨haZ, h ▸ (Subgroup.mem_inf.1 ha).2⟩
      rw [hbot] at this
      exact this
  exfalso
  have hu : UType V W Z Z₂ a := by rw [← hdec]; exact P.utype_of_decomp hZ hz hz₂ hz1 hz₂1
  exact hnot a _ hu hk hk1 k rfl

end S4Pair

end CFSG.CGT.PushingUpLit.A78S4
