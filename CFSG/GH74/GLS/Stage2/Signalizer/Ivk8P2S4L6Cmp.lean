module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4Comp
import CFSG.GH74.AS16.Standard
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpLift

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Basic

variable {G : Type} [Group G]

theorem ka6cmp_commute {I₁ I₂ : Subgroup G} (h : ⁅I₁, I₂⁆ = ⊥) :
    ∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a := by
  intro a ha b hb
  exact (Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha) b hb).symm

theorem ka6cmp_eq_one_of_odd {H : Type*} [Group H] (hH : Odd (Nat.card H)) {x : H}
    (hx : x ^ 2 = 1) : x = 1 := by
  have hcard : x ^ Nat.card H = 1 := pow_card_eq_one'
  have hgcd : x ^ Nat.gcd 2 (Nat.card H) = 1 := pow_gcd_eq_one.mpr ⟨hx, hcard⟩
  rwa [(Nat.coprime_two_left.mpr hH).gcd_eq_one, pow_one] at hgcd

theorem ka6cmp_normal {I₁ I₂ : Subgroup G} (hc : ∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a) :
    (I₂.subgroupOf I₁).Normal := by
  refine Subgroup.normal_of_le_center fun n hn => ?_
  rw [Subgroup.mem_center_iff]
  intro x
  exact Subtype.ext (hc x x.2 n hn)

theorem ka6cmp_odd_card [Finite G] {I₁ I₂ J : Subgroup G}
    (hc : ∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a) (hJT : J ≤ I₁ ⊔ I₂)
    (hinv : ∀ d : G, orderOf d = 2 → ¬ J ≤ centralizer ({d} : Set G)) :
    Odd (Nat.card ↥(I₂.subgroupOf I₁)) := by
  by_contra hodd
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heven : 2 ∣ Nat.card ↥(I₂.subgroupOf I₁) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := ↥(I₂.subgroupOf I₁)) 2 heven
  have hd2 : orderOf (((d : ↥I₁) : G)) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hd]
  have hdI₂ : ((d : ↥I₁) : G) ∈ I₂ := d.2
  have hdI₁ : ((d : ↥I₁) : G) ∈ I₁ := (d : ↥I₁).2
  refine hinv _ hd2 fun x hx => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := P2S4.exists_mul_of_mem_sup hc (hJT hx)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc a * b * ((d : ↥I₁) : G) = a * (b * ((d : ↥I₁) : G)) := mul_assoc _ _ _
    _ = a * (((d : ↥I₁) : G) * b) := by rw [← hc _ hdI₁ b hb]
    _ = (a * ((d : ↥I₁) : G)) * b := (mul_assoc _ _ _).symm
    _ = (((d : ↥I₁) : G) * a) * b := by rw [hc a ha _ hdI₂]
    _ = ((d : ↥I₁) : G) * (a * b) := mul_assoc _ _ _

theorem ka6cmp_inf_bot [Finite G] {I₁ I₂ J W₁ W₂ : Subgroup G}
    (hc : ∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a) (hJT : J ≤ I₁ ⊔ I₂)
    (hinv : ∀ d : G, orderOf d = 2 → ¬ J ≤ centralizer ({d} : Set G)) (hW₁ : W₁ ≤ I₁)
    (hW₂ : W₂ ≤ I₂) (hW₁el : IsElementaryAbelian 2 ↥W₁) : W₁ ⊓ W₂ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hx2 : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := W₁) x hx.1
  let y : ↥(I₂.subgroupOf I₁) := ⟨⟨x, hW₁ hx.1⟩, hW₂ hx.2⟩
  have hy : y ^ 2 = 1 := Subtype.ext (Subtype.ext hx2)
  exact congrArg (fun z : ↥(I₂.subgroupOf I₁) => ((z : ↥I₁) : G))
    (ka6cmp_eq_one_of_odd (ka6cmp_odd_card hc hJT hinv) hy)

end Basic

section Proj

variable {G : Type} [Group G]

theorem ka6cmp_exists_proj {I₁ I₂ J : Subgroup G} [(I₂.subgroupOf I₁).Normal]
    (hc : ∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a) (hJT : J ≤ I₁ ⊔ I₂) :
    ∃ f : ↥J →* ↥I₁ ⧸ I₂.subgroupOf I₁,
      (∀ (j : ↥J) (a : ↥I₁) (b : G), b ∈ I₂ → (a : G) * b = (j : G) →
        f j = QuotientGroup.mk a) ∧ ∀ j : ↥J, f j = 1 → (j : G) ∈ I₂ := by
  have hdec : ∀ j : ↥J, ∃ a : ↥I₁, ∃ b : G, b ∈ I₂ ∧ (a : G) * b = (j : G) := by
    intro j
    obtain ⟨a, ha, b, hb, hab⟩ := P2S4.exists_mul_of_mem_sup hc (hJT j.2)
    exact ⟨⟨a, ha⟩, b, hb, hab⟩
  have huniq : ∀ (a c : ↥I₁) (b d : G), b ∈ I₂ → d ∈ I₂ → (a : G) * b = (c : G) * d →
      (QuotientGroup.mk a : ↥I₁ ⧸ I₂.subgroupOf I₁) = QuotientGroup.mk c := by
    intro a c b d hb hd h
    rw [QuotientGroup.eq]
    show ((a⁻¹ * c : ↥I₁) : G) ∈ I₂
    have hc' : (c : G) = (a : G) * b * (d : G)⁻¹ := eq_mul_inv_of_mul_eq h.symm
    have e : ((a⁻¹ * c : ↥I₁) : G) = b * (d : G)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hc']
      group
    rw [e]
    exact I₂.mul_mem hb (I₂.inv_mem hd)
  let f : ↥J →* ↥I₁ ⧸ I₂.subgroupOf I₁ :=
    { toFun := fun j => QuotientGroup.mk (hdec j).choose
      map_one' := by
        obtain ⟨b, hb, hab⟩ := (hdec 1).choose_spec
        have := huniq (hdec 1).choose 1 b 1 hb I₂.one_mem (by simpa using hab)
        simpa using this
      map_mul' := by
        intro x y
        obtain ⟨bx, hbx, habx⟩ := (hdec x).choose_spec
        obtain ⟨by', hby, haby⟩ := (hdec y).choose_spec
        obtain ⟨b, hb, hab⟩ := (hdec (x * y)).choose_spec
        show (QuotientGroup.mk (hdec (x * y)).choose : ↥I₁ ⧸ I₂.subgroupOf I₁) =
          QuotientGroup.mk (hdec x).choose * QuotientGroup.mk (hdec y).choose
        rw [← QuotientGroup.mk_mul]
        refine huniq _ _ b (bx * by') hb (I₂.mul_mem hbx hby) ?_
        have h1 := hc ((hdec y).choose : G) ((hdec y).choose).2 bx hbx
        calc ((hdec (x * y)).choose : G) * b = ((x * y : ↥J) : G) := hab
          _ = (x : G) * (y : G) := rfl
          _ = (((hdec x).choose : G) * bx) * (((hdec y).choose : G) * by') := by
            rw [habx, haby]
          _ = ((hdec x).choose : G) * (bx * ((hdec y).choose : G)) * by' := by group
          _ = ((hdec x).choose : G) * (((hdec y).choose : G) * bx) * by' := by rw [h1]
          _ = (((hdec x).choose * (hdec y).choose : ↥I₁) : G) * (bx * by') := by
            rw [Subgroup.coe_mul]
            group }
  refine ⟨f, fun j a b hb hab => ?_, fun j hj => ?_⟩
  · obtain ⟨b₀, hb₀, hab₀⟩ := (hdec j).choose_spec
    exact huniq _ a b₀ b hb₀ hb (hab₀.trans hab.symm)
  · obtain ⟨b₀, hb₀, hab₀⟩ := (hdec j).choose_spec
    have h1 : (hdec j).choose ∈ I₂.subgroupOf I₁ := (QuotientGroup.eq_one_iff _).mp hj
    have h2 : (((hdec j).choose : ↥I₁) : G) ∈ I₂ := h1
    rw [← hab₀]
    exact I₂.mul_mem h2 hb₀

end Proj

section Rank

variable {G : Type} [Group G]

theorem ka6cmp_card_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (H : Subgroup X)
    (hf : ∀ x ∈ H, f x = 1 → x = 1) : Nat.card ↥(H.map f) = Nat.card ↥H := by
  have hinj : Function.Injective (f.comp H.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hf x x.2 hx)
  have hrange : (f.comp H.subtype).range = H.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem ka6cmp_isElementaryAbelian_of_injective {p : ℕ} {A Y : Type*} [Group A] [Group Y]
    {E : Subgroup Y} (hE : IsElementaryAbelian p ↥E) (f : A →* Y) (hf : Function.Injective f)
    (hfE : ∀ a, f a ∈ E) : IsElementaryAbelian p A := by
  refine { toIsMulCommutative := ⟨⟨fun a b => hf ?_⟩⟩, exponent_dvd_p := ?_ }
  · rw [map_mul, map_mul]
    exact congrArg Subtype.val ((hE.toIsMulCommutative.is_comm).comm
      (⟨f a, hfE a⟩ : E) ⟨f b, hfE b⟩)
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => hf ?_
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) (f a) (hfE a)

theorem ka6cmp_two [Finite G] {J A I₁ I₂ : Subgroup G} (hq : IsQuasisimple ↥J)
    (hZ : Odd (Nat.card ↥(center ↥J))) (hAJ : A ≤ J) (hAel : IsElementaryAbelian 2 ↥A)
    (hAcard : Nat.card ↥A = 2 ^ 4)
    (hinv : ∀ d : G, orderOf d = 2 → ¬ J ≤ centralizer ({d} : Set G))
    (hc : ∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a) (hJT : J ≤ I₁ ⊔ I₂) (hJ₂ : ¬ J ≤ I₂) :
    ∃ W : Subgroup G, W ≤ I₁ ∧ IsElementaryAbelian 2 ↥W ∧ Nat.card ↥W = 2 ^ 4 := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNn : (I₂.subgroupOf I₁).Normal := ka6cmp_normal hc
  have hNodd : Odd (Nat.card ↥(I₂.subgroupOf I₁)) := ka6cmp_odd_card hc hJT hinv
  obtain ⟨f, -, hker⟩ := ka6cmp_exists_proj (J := J) hc hJT
  have hkc : f.ker ≤ center ↥J := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq f.normal_ker with htop | hle
    · exfalso
      refine hJ₂ fun x hx => hker ⟨x, hx⟩ ?_
      have hmem : (⟨x, hx⟩ : ↥J) ∈ f.ker := by rw [htop]; trivial
      exact MonoidHom.mem_ker.mp hmem
    · exact hle
  have hA'el : IsElementaryAbelian 2 ↥(A.subgroupOf J) := IsElementaryAbelian.subgroupOf hAJ
  have hinjA : ∀ x ∈ A.subgroupOf J, f x = 1 → x = 1 := by
    intro x hx hfx
    have hxc : x ∈ center ↥J := hkc (MonoidHom.mem_ker.mpr hfx)
    have hx2 : x ^ 2 = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A.subgroupOf J) x hx
    have hy : (⟨x, hxc⟩ : ↥(center ↥J)) = 1 :=
      ka6cmp_eq_one_of_odd hZ (Subtype.ext hx2 : (⟨x, hxc⟩ : ↥(center ↥J)) ^ 2 = 1)
    exact congrArg Subtype.val hy
  let W : Subgroup (↥I₁ ⧸ I₂.subgroupOf I₁) := (A.subgroupOf J).map f
  have hWel : IsElementaryAbelian 2 ↥W := IsElementaryAbelian.map f
  have hWcard : Nat.card ↥W = 2 ^ 4 := by
    rw [ka6cmp_card_map f (A.subgroupOf J) hinjA, ← hAcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAJ).toEquiv
  obtain ⟨W', -, hmap, hbot⟩ :=
    Odd87.exists_two_lift (I₂.subgroupOf I₁) hNodd W (IsElementaryAbelian.isPGroup 2 ↥W)
  have hinjW : ∀ x ∈ W', QuotientGroup.mk' (I₂.subgroupOf I₁) x = 1 → x = 1 := by
    intro x hx hx1
    have hxN : x ∈ I₂.subgroupOf I₁ := (QuotientGroup.eq_one_iff x).mp hx1
    have hxb : x ∈ W' ⊓ I₂.subgroupOf I₁ := ⟨hx, hxN⟩
    rw [hbot, Subgroup.mem_bot] at hxb
    exact hxb
  have hW'card : Nat.card ↥W' = 2 ^ 4 := by
    rw [← ka6cmp_card_map (QuotientGroup.mk' (I₂.subgroupOf I₁)) W' hinjW, hmap]
    exact hWcard
  have hW'el : IsElementaryAbelian 2 ↥W' := by
    refine ka6cmp_isElementaryAbelian_of_injective hWel
      ((QuotientGroup.mk' (I₂.subgroupOf I₁)).comp W'.subtype) ?_ ?_
    · rw [injective_iff_map_eq_one]
      intro x hx
      exact Subtype.ext (hinjW x x.2 hx)
    · intro x
      have hxW : QuotientGroup.mk' (I₂.subgroupOf I₁) (x : ↥I₁) ∈ W'.map
          (QuotientGroup.mk' (I₂.subgroupOf I₁)) := Subgroup.mem_map_of_mem _ x.2
      rw [hmap] at hxW
      exact hxW
  refine ⟨W'.map I₁.subtype, Subgroup.map_subtype_le W', IsElementaryAbelian.map_subtype, ?_⟩
  rw [Subgroup.card_map_of_injective I₁.subtype_injective, hW'card]

theorem ka6cmp_rank [Finite G] {W₁ W₂ : Subgroup G} (hW₁el : IsElementaryAbelian 2 ↥W₁)
    (hW₂el : IsElementaryAbelian 2 ↥W₂) (hW₁card : Nat.card ↥W₁ = 2 ^ 4)
    (hW₂card : Nat.card ↥W₂ = 2 ^ 4) (hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a)
    (hbot : W₁ ⊓ W₂ = ⊥) : 8 ≤ pRank 2 G := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCE : W₂ ≤ centralizer (W₁ : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => hcomm a ha b hb
  have hel : IsElementaryAbelian 2 ↥(W₁ ⊔ W₂) := IsElementaryAbelian.sup_of_le_centralizer hCE
  let g : ↥W₁ × ↥W₂ → ↥(W₁ ⊔ W₂) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hg : Function.Injective g := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    have h1 : (x : G) * y = x' * y' := congrArg Subtype.val h
    have hmem : (x' : G)⁻¹ * x ∈ W₁ ⊓ W₂ := by
      refine ⟨W₁.mul_mem (W₁.inv_mem x'.2) x.2, ?_⟩
      have e : (x' : G)⁻¹ * x = y' * (y : G)⁻¹ := by
        calc (x' : G)⁻¹ * x = (x' : G)⁻¹ * (x * y) * (y : G)⁻¹ := by group
          _ = (x' : G)⁻¹ * (x' * y') * (y : G)⁻¹ := by rw [h1]
          _ = y' * (y : G)⁻¹ := by group
      rw [e]
      exact W₂.mul_mem y'.2 (W₂.inv_mem y.2)
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    have hx : x = x' := Subtype.ext hmem.symm
    subst hx
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel h1))
  have hle : Nat.card (↥W₁ × ↥W₂) ≤ Nat.card ↥(W₁ ⊔ W₂) := Nat.card_le_card_of_injective g hg
  rw [Nat.card_prod, hW₁card, hW₂card] at hle
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp (IsElementaryAbelian.isPGroup 2 ↥(W₁ ⊔ W₂))
  have h8 : 2 ^ 8 ≤ 2 ^ m := by
    rw [← hm]
    calc 2 ^ 8 = 2 ^ 4 * 2 ^ 4 := by norm_num
      _ ≤ _ := hle
  have hm8 : 8 ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).mp h8
  exact hm8.trans (P2S4.le_pRank_of_card one_lt_two (W₁ ⊔ W₂) hel hm)

end Rank

theorem exists_comp_of_le_Em {G : Type} [Group G] [Finite G] {K J : Subgroup G}
    (hq : IsQuasisimple ↥J) (hZ : Odd (Nat.card ↥(center ↥J)))
    (hA : ∃ A : Subgroup G, A ≤ J ∧ IsElementaryAbelian 2 ↥A ∧ Nat.card ↥A = 2 ^ 4)
    (hinv : ∀ d : G, orderOf d = 2 → ¬ J ≤ centralizer ({d} : Set G))
    (hG : pRank 2 G ≤ 4)
    (hno3 : ∀ I₁ I₂ I₃ : Subgroup G, IsCompIn K I₁ → IsCompIn K I₂ → IsCompIn K I₃ →
      I₁ = I₂ ∨ I₁ = I₃ ∨ I₂ = I₃)
    (hJE : J ≤ Em K) : ∃ I : Subgroup G, IsCompIn K I ∧ J ≤ I := by
  obtain ⟨A, hAJ, hAel, hAcard⟩ := hA
  by_contra hno
  have hno' : ∀ I : Subgroup G, IsCompIn K I → ¬ J ≤ I := fun I hI hJI => hno ⟨I, hI, hJI⟩
  by_cases hex : ∃ I : Subgroup G, IsCompIn K I
  · obtain ⟨I₁, hI₁⟩ := hex
    by_cases hall : ∀ I : Subgroup G, IsCompIn K I → I = I₁
    · exact hno' I₁ hI₁ (hJE.trans (P2S4.Em_le_of_comps_le fun I hI => (hall I hI).le))
    · push Not at hall
      obtain ⟨I₂, hI₂, hne⟩ := hall
      have hcomm : ∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a :=
        ka6cmp_commute ((AS16.isCompIn_commute hI₁ hI₂).resolve_left hne.symm)
      have hJT : J ≤ I₁ ⊔ I₂ := hJE.trans (P2S4.Em_le_of_comps_le fun I hI => by
        rcases hno3 I₁ I₂ I hI₁ hI₂ hI with h | h | h
        · exact absurd h hne.symm
        · rw [← h]
          exact le_sup_left
        · rw [← h]
          exact le_sup_right)
      have hcomm' : ∀ a ∈ I₂, ∀ b ∈ I₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
      have hJT' : J ≤ I₂ ⊔ I₁ := hJT.trans (sup_comm I₁ I₂).le
      obtain ⟨W₁, hW₁, hW₁el, hW₁card⟩ :=
        ka6cmp_two hq hZ hAJ hAel hAcard hinv hcomm hJT (hno' I₂ hI₂)
      obtain ⟨W₂, hW₂, hW₂el, hW₂card⟩ :=
        ka6cmp_two hq hZ hAJ hAel hAcard hinv hcomm' hJT' (hno' I₁ hI₁)
      have h8 := ka6cmp_rank hW₁el hW₂el hW₁card hW₂card
        (fun a ha b hb => hcomm a (hW₁ ha) b (hW₂ hb))
        (ka6cmp_inf_bot hcomm hJT hinv hW₁ hW₂ hW₁el)
      omega
  · have hbot : Em K ≤ ⊥ := P2S4.Em_le_of_comps_le fun I hI => absurd ⟨I, hI⟩ hex
    have hAbot : A = ⊥ := le_bot_iff.mp (hAJ.trans (hJE.trans hbot))
    rw [hAbot, Subgroup.card_bot] at hAcard
    norm_num at hAcard

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
