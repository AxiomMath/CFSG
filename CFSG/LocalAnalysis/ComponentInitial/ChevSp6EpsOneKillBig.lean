module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillCert
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneGqFacts
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillCoset
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillSignBase
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillSylowBase

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

open Subgroup

theorem inv_mem_of_closed {H : Type*} [Group H] [Finite H] {S : Set H} (h1 : (1 : H) ∈ S)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) {x : H} (hx : x ∈ S) : x⁻¹ ∈ S := by
  have hpow : ∀ k : ℕ, x ^ k ∈ S := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact h1
    | succ k ih => rw [pow_succ]; exact hmul _ ih _ hx
  have hn := orderOf_pos x
  have e : x⁻¹ = x ^ (orderOf x - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hn, pow_orderOf_eq_one]
  rw [e]
  exact hpow _

theorem exists_subgroup_of_list {u : Bool} {L : List (List ℕ)} (hid : idT ∈ L)
    (hmul : ∀ a ∈ L, ∀ b ∈ L, compT a b ∈ L) (hL : ∀ x ∈ L, ∃ σ ∈ Gq u, tupleOf σ = x)
    (hnd : L.Nodup) :
    ∃ R : Subgroup (Equiv.Perm (Fin 64)), (∀ σ, σ ∈ R ↔ σ ∈ Gq u ∧ tupleOf σ ∈ L) ∧
      Nat.card R = L.length := by
  let S : Set (Equiv.Perm (Fin 64)) := {σ | σ ∈ Gq u ∧ tupleOf σ ∈ L}
  have h1 : (1 : Equiv.Perm (Fin 64)) ∈ S := ⟨one_mem _, by rw [tupleOf_one]; exact hid⟩
  have hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S := fun a ha b hb =>
    ⟨mul_mem ha.1 hb.1, by rw [tupleOf_mul ha.1.1]; exact hmul _ ha.2 _ hb.2⟩
  let R : Subgroup (Equiv.Perm (Fin 64)) :=
    { carrier := S
      mul_mem' := fun ha hb => hm _ ha _ hb
      one_mem' := h1
      inv_mem' := fun hx => inv_mem_of_closed h1 hm hx }
  refine ⟨R, fun σ => Iff.rfl, ?_⟩
  have hbij : Function.Bijective (fun σ : R => (⟨tupleOf σ, σ.2.2⟩ : {x // x ∈ L})) := by
    refine ⟨fun σ σ' hs => Subtype.ext (tupleOf_injective σ.2.1.1 σ'.2.1.1
      (congrArg Subtype.val hs)), fun x => ?_⟩
    obtain ⟨σ, hσ, he⟩ := hL x.1 x.2
    exact ⟨⟨σ, hσ, he ▸ x.2⟩, Subtype.ext he⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), ← List.toFinset_card_of_nodup hnd,
    ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun l => List.mem_toFinset.symm)

theorem mem_of_code_mem {L : List (List ℕ)} (hgood : ∀ x ∈ L, Good x) {a : List ℕ} (ha : Good a)
    (hc : codeT a ∈ L.map codeT) : a ∈ L := by
  obtain ⟨b, hb, hba⟩ := List.mem_map.1 hc
  rw [← codeT_inj_good (hgood b hb) ha hba]
  exact hb

theorem validCert_spec {u : Bool} {l : List ℕ} (hl : Good l) {c : List (List ℕ) × ℕ × ℕ}
    (h : validCert u l c = true) :
    let els := c.1.map (evalW l)
    0 < els.length ∧ (∃ k, k < 9 ∧ els.length = 2 ^ k) ∧ els.Nodup ∧ idT ∈ els ∧ l ∈ els ∧
      (∀ a ∈ els, ∀ b ∈ els, compT a b ∈ els) ∧ (∀ a ∈ els, compT a l = compT l a) ∧
      (fixV l).length * ((List.range 512).filter fun e => evalE (bOf u l) e == e).length ≤
        32 * els.length ∧
      c.2.1 < 64 ∧ c.2.2 < 64 ∧ evalV l c.2.1 = c.2.1 ∧ evalV l c.2.2 = c.2.2 ∧
      ∀ e, e < 512 → evalE (bOf u l) e ^^^ e ≠ betaOf u c.2.1 c.2.2 := by
  intro els
  have hgood : ∀ x ∈ els, Good x := fun x hx => by
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
    exact good_evalW hl w
  simp only [validCert, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.contains_iff_mem,
    List.all_eq_true, Bool.not_eq_true', List.any_eq_false, List.mem_range, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpos, hpow⟩, hnd⟩, hid⟩, hl'⟩, hcl⟩, hcomm⟩, hfix⟩, hv⟩, hw⟩, hfv⟩,
    hfw⟩, hβ⟩ := h
  refine ⟨hpos, hpow,
    List.Nodup.of_map codeT hnd, mem_of_code_mem hgood ⟨rfl, by decide⟩ hid,
    mem_of_code_mem hgood hl hl', fun a ha b hb => mem_of_code_mem hgood
      (good_compT (hgood a ha) (hgood b hb)) (hcl a ha b hb), hcomm, hfix, hv, hw, hfv, hfw,
    fun e he hbe => hβ e he hbe⟩

theorem isPGroup_zpowers_of_sq {G : Type*} [Group G] {t : G} (ht2 : t * t = 1) :
    IsPGroup 2 (zpowers t) := by
  rintro ⟨g, hg⟩
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, ht2, one_zpow]

namespace KillData

variable {G : Type*} [Group G] {u : Bool} {Jh E : Subgroup G} {cV cE : G → ℕ}
  {z l₁ l₂ : G} (h : KillData u Jh E cV cE z l₁ l₂)

open Classical in
@[expose] noncomputable def actP (x : G) : Equiv.Perm (Fin 64) :=
  if hx : x ∈ normalizer (Jh : Set G) then h.ρV ⟨x, hx⟩ else 1

include h

theorem actP_of_mem {x : G} (hx : x ∈ normalizer (Jh : Set G)) : h.actP x = h.ρV ⟨x, hx⟩ :=
  dite_eq_left hx

theorem actP_mul {x y : G} (hx : x ∈ normalizer (Jh : Set G)) (hy : y ∈ normalizer (Jh : Set G)) :
    h.actP (x * y) = h.actP x * h.actP y := by
  rw [h.actP_of_mem (mul_mem hx hy), h.actP_of_mem hx, h.actP_of_mem hy, ← map_mul]
  rfl

theorem actP_inv {x : G} (hx : x ∈ normalizer (Jh : Set G)) : h.actP x⁻¹ = (h.actP x)⁻¹ := by
  rw [h.actP_of_mem (inv_mem hx), h.actP_of_mem hx, ← map_inv]
  rfl

theorem actP_eq_one_of_mem_Jh {j : G} (hj : j ∈ Jh) : h.actP j = 1 := by
  obtain ⟨y, hy, hyj⟩ := h.Jh_le_Kk hj
  rw [h.actP_of_mem (Jh_le_X hj)]
  have : (⟨j, Jh_le_X hj⟩ : normalizer (Jh : Set G)) = y := Subtype.ext hyj.symm
  rw [this]
  exact MonoidHom.mem_ker.1 hy

theorem mem_Kk_of_actP {x : G} (hx : x ∈ normalizer (Jh : Set G)) (h1 : h.actP x = 1) :
    x ∈ h.Kk :=
  ⟨⟨x, hx⟩, MonoidHom.mem_ker.2 (by rw [← h.actP_of_mem hx]; exact h1), rfl⟩

section Lift

variable [Finite G]

theorem exists_lift {Rb : Subgroup (Equiv.Perm (Fin 64))} (hRb : IsPGroup 2 Rb)
    (hsurj : ∀ τ ∈ Rb, ∃ x, ∃ hx : x ∈ normalizer (Jh : Set G), h.ρV ⟨x, hx⟩ = τ)
    {t : G} (ht : t ∈ normalizer (Jh : Set G)) (ht2 : t * t = 1) (htR : h.actP t ∈ Rb) :
    ∃ R : Subgroup G, IsPGroup 2 R ∧ Jh ≤ R ∧ t ∈ R ∧
      (∀ r ∈ R, r ∈ normalizer (Jh : Set G) ∧ h.actP r ∈ Rb) ∧
      2 ^ 15 * Nat.card Rb ≤ Nat.card R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let YG : Subgroup G :=
    { carrier := {x | x ∈ normalizer (Jh : Set G) ∧ h.actP x ∈ Rb}
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
        rw [h.actP_mul hx.1 hy.1]; exact mul_mem hx.2 hy.2⟩
      one_mem' := ⟨one_mem _, by
        rw [h.actP_of_mem (one_mem _), show (⟨1, one_mem _⟩ : normalizer (Jh : Set G)) = 1
          from rfl, map_one]; exact one_mem _⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [h.actP_inv hx.1]; exact inv_mem hx.2⟩ }
  let f : YG →* Rb :=
    { toFun := fun y => ⟨h.actP y, y.2.2⟩
      map_one' := Subtype.ext (by
        show h.actP 1 = 1
        rw [h.actP_of_mem (one_mem _), show (⟨1, one_mem _⟩ : normalizer (Jh : Set G)) = 1
          from rfl, map_one])
      map_mul' := fun x y => Subtype.ext (h.actP_mul x.2.1 y.2.1) }
  have hf : Function.Surjective f := by
    intro τ
    obtain ⟨x, hx, hxτ⟩ := hsurj τ τ.2
    have hxY : x ∈ YG := ⟨hx, by rw [h.actP_of_mem hx, hxτ]; exact τ.2⟩
    exact ⟨⟨x, hxY⟩, Subtype.ext (by show h.actP x = τ; rw [h.actP_of_mem hx, hxτ])⟩
  have hJY : Jh ≤ YG := fun j hj =>
    ⟨Jh_le_X hj, by rw [h.actP_eq_one_of_mem_Jh hj]; exact one_mem _⟩
  have htY : t ∈ YG := ⟨ht, htR⟩
  have hJz : IsPGroup 2 (Jh ⊔ zpowers t : Subgroup G) :=
    h.isPGroup_Jh.to_sup_of_normal_left' (isPGroup_zpowers_of_sq ht2) (zpowers_le.2 ht)
  have hJzY : (Jh ⊔ zpowers t : Subgroup G) ≤ YG := sup_le hJY (zpowers_le.2 htY)
  obtain ⟨R₀, hR₀⟩ :=
    (hJz.comap_of_injective YG.subtype (Subgroup.subtype_injective _)).exists_le_sylow
  refine ⟨(R₀ : Subgroup YG).map YG.subtype, R₀.2.map _, fun j hj => ⟨⟨j, hJY hj⟩,
    hR₀ (Subgroup.mem_subgroupOf.2 (mem_sup_left hj)), rfl⟩, ⟨⟨t, htY⟩,
    hR₀ (Subgroup.mem_subgroupOf.2 (mem_sup_right (mem_zpowers t))), rfl⟩, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  ·
    have himg : (R₀ : Subgroup YG).map f = ⊤ := by
      have htop : IsPGroup 2 (⊤ : Subgroup Rb) := hRb.of_equiv (Subgroup.topEquiv).symm
      have := (R₀.mapSurjective hf).3 htop le_top
      rw [Sylow.coe_mapSurjective] at this
      exact this.symm
    have hcard := card_ker_mul_card_range (f.comp (R₀ : Subgroup YG).subtype)
    have hrange : (f.comp (R₀ : Subgroup YG).subtype).range = ⊤ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, himg]
    rw [hrange, Subgroup.card_top] at hcard
    have hker : 2 ^ 15 ≤ Nat.card (f.comp (R₀ : Subgroup YG).subtype).ker := by
      rw [← h.card_Jh]
      refine Nat.card_le_card_of_injective (fun j : Jh => (⟨⟨⟨j, hJY j.2⟩,
        hR₀ (Subgroup.mem_subgroupOf.2 (mem_sup_left j.2))⟩, MonoidHom.mem_ker.2 (Subtype.ext ?_)⟩ :
          (f.comp (R₀ : Subgroup YG).subtype).ker)) ?_
      · show h.actP j = 1
        exact h.actP_eq_one_of_mem_Jh j.2
      · intro a b hab
        exact Subtype.ext (congrArg (fun x : (f.comp (R₀ : Subgroup YG).subtype).ker =>
          (((x : R₀) : YG) : G)) hab)
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), ← hcard]
    exact Nat.mul_le_mul_right _ hker

end Lift

section Count

variable [Finite G]

theorem card_le_inv_mul_cent {R : Subgroup G} (hR : IsPGroup 2 R) (hJR : Jh ≤ R) {t : G}
    (htR : t ∈ R) (ht : t ∈ normalizer (Jh : Set G)) (ht2 : t * t = 1)
    (hRX : ∀ r ∈ R, r ∈ normalizer (Jh : Set G) ∧ h.actP r * h.actP t = h.actP t * h.actP r) :
    Nat.card R ≤ Nat.card {j : Jh // (t * j) * (t * j) = 1} *
      Nat.card (R ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  classical
  have hRK : ∀ x ∈ R, x ∈ h.Kk → x ∈ Jh := by
    intro x hxR hxK
    have hP : IsPGroup 2 (R ⊓ h.Kk : Subgroup G) := hR.to_le inf_le_left
    have heq : Jh = R ⊓ h.Kk := Subgroup.eq_of_le_of_card_ge (le_inf hJR h.Jh_le_Kk) (by
      rw [h.card_Jh]; exact h.card_le_of_le_Kk hP inf_le_right)
    rw [heq]; exact ⟨hxR, hxK⟩
  let I := {j : Jh // (t * j) * (t * j) = 1}
  have hψ : ∀ r : R, t⁻¹ * ((r : G) * t * (r : G)⁻¹) ∈ Jh ∧
      (t * (t⁻¹ * ((r : G) * t * (r : G)⁻¹))) * (t * (t⁻¹ * ((r : G) * t * (r : G)⁻¹))) = 1 := by
    intro r
    obtain ⟨hrX, hrc⟩ := hRX r r.2
    refine ⟨hRK _ (mul_mem (inv_mem htR) (mul_mem (mul_mem r.2 htR) (inv_mem r.2)))
      (h.mem_Kk_of_actP (mul_mem (inv_mem ht) (mul_mem (mul_mem hrX ht) (inv_mem hrX))) ?_), ?_⟩
    · rw [h.actP_mul (inv_mem ht) (mul_mem (mul_mem hrX ht) (inv_mem hrX)),
        h.actP_mul (mul_mem hrX ht) (inv_mem hrX), h.actP_mul hrX ht, h.actP_inv ht,
        h.actP_inv hrX, hrc]
      group
    · calc (t * (t⁻¹ * ((r : G) * t * (r : G)⁻¹))) * (t * (t⁻¹ * ((r : G) * t * (r : G)⁻¹)))
          = (r : G) * (t * t) * (r : G)⁻¹ := by group
        _ = 1 := by rw [ht2]; group
  let ψ : R → I := fun r => ⟨⟨_, (hψ r).1⟩, (hψ r).2⟩
  let sec : I → R := fun i => if hi : ∃ r, ψ r = i then Classical.choose hi else 1
  have hsec : ∀ r : R, ψ (sec (ψ r)) = ψ r := by
    intro r
    have hi : ∃ r', ψ r' = ψ r := ⟨r, rfl⟩
    simp only [sec, dite_eq_left hi]
    exact Classical.choose_spec hi
  have hC : ∀ r : R, ((sec (ψ r) : G))⁻¹ * r ∈ (R ⊓ centralizer ({t} : Set G) : Subgroup G) := by
    intro r
    refine ⟨R.mul_mem (R.inv_mem (sec (ψ r)).2) r.2, mem_centralizer_singleton_iff.2 ?_⟩
    have e := congrArg (fun i : I => ((i : Jh) : G)) (hsec r)
    simp only [ψ] at e
    have e2 : (sec (ψ r) : G) * t * (sec (ψ r) : G)⁻¹ = (r : G) * t * (r : G)⁻¹ := by
      have := congrArg (t * ·) e
      simpa using this
    calc ((sec (ψ r) : G))⁻¹ * r * t
        = (sec (ψ r) : G)⁻¹ * ((r : G) * t * (r : G)⁻¹) * r := by group
      _ = (sec (ψ r) : G)⁻¹ * ((sec (ψ r) : G) * t * (sec (ψ r) : G)⁻¹) * r := by rw [e2]
      _ = t * ((sec (ψ r) : G)⁻¹ * r) := by group
  let Φ : R → I × (R ⊓ centralizer ({t} : Set G) : Subgroup G) := fun r => (ψ r, ⟨_, hC r⟩)
  have hΦ : Function.Injective Φ := by
    intro r r' hrr
    have h1 : ψ r = ψ r' := congrArg Prod.fst hrr
    have h2 : ((sec (ψ r) : G))⁻¹ * r = ((sec (ψ r') : G))⁻¹ * r' :=
      congrArg (fun p => ((p.2 : (R ⊓ centralizer ({t} : Set G) : Subgroup G)) : G)) hrr
    rw [h1] at h2
    exact Subtype.ext (mul_left_cancel h2)
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective Φ hΦ

end Count

section Kill

variable [Finite G]

theorem exists_big_of_validCert {t : G} (ht : t ∈ normalizer (Jh : Set G)) (ht2 : t * t = 1)
    {c : List (List ℕ) × ℕ × ℕ} (hcert : validCert u (tupleOf (h.ρV ⟨t, ht⟩)) c = true) :
    ∃ C : Subgroup G, C ≤ centralizer ({t} : Set G) ∧ IsPGroup 2 C ∧ 2 ^ 11 ≤ Nat.card C := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := h.ρV ⟨t, ht⟩ with hσdef
  have hσG : σ ∈ Gq u := h.ρV_mem_Gq _
  have hactt : h.actP t = σ := h.actP_of_mem ht
  have hgl : Good (tupleOf σ) := good_tupleOf σ
  obtain ⟨hpos, hpow, hnd, hid, hlm, hcl, hcomm, hfix, hv₀, hw₀, hfv₀, hfw₀, hβ⟩ :=
    validCert_spec hgl hcert
  generalize hels : c.1.map (evalW (tupleOf σ)) = els at *
  have hword : ∀ x ∈ els, ∃ w, tupleOf (h.ρV ⟨evalWG z l₁ l₂ t w, h.evalWG_mem ht w⟩) = x := by
    intro x hx
    rw [← hels] at hx
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
    exact ⟨w, h.tupleOf_evalWG ht w⟩
  obtain ⟨Rb, hRb, hRbc⟩ := exists_subgroup_of_list (u := u) hid hcl (fun x hx => by
    obtain ⟨w, hw⟩ := hword x hx
    exact ⟨_, h.ρV_mem_Gq _, hw⟩) hnd
  have hRb2 : IsPGroup 2 Rb := by
    obtain ⟨k, -, hk⟩ := hpow
    exact IsPGroup.of_card (n := k) (by rw [hRbc, hk])
  have hsurj : ∀ τ ∈ Rb, ∃ x, ∃ hx : x ∈ normalizer (Jh : Set G), h.ρV ⟨x, hx⟩ = τ := by
    intro τ hτ
    obtain ⟨hτG, hτL⟩ := (hRb τ).1 hτ
    obtain ⟨w, hw⟩ := hword _ hτL
    exact ⟨_, h.evalWG_mem ht w, tupleOf_injective (h.ρV_mem_Gq _).1 hτG.1 hw⟩
  have hRbcent : ∀ τ ∈ Rb, τ * σ = σ * τ := by
    intro τ hτ
    obtain ⟨hτG, hτL⟩ := (hRb τ).1 hτ
    exact tupleOf_injective (mul_mem hτG hσG).1 (mul_mem hσG hτG).1 (by
      rw [tupleOf_mul hτG.1, tupleOf_mul hσG.1]; exact hcomm _ hτL)
  have hσR : h.actP t ∈ Rb := by rw [hactt]; exact (hRb σ).2 ⟨hσG, hlm⟩
  obtain ⟨R, hR2, hJR, htR, hRX, hRcard⟩ := h.exists_lift hRb2 hsurj ht ht2 hσR
  have hcount := h.card_le_inv_mul_cent hR2 hJR htR ht ht2 fun r hr =>
    ⟨(hRX r hr).1, by rw [hactt]; exact hRbcent _ (hRX r hr).2⟩
  have hfv : h.actV t c.2.1 = c.2.1 := by
    have := hfv₀
    rw [evalV_tupleOf hσG.1 hv₀, fn, dite_eq_left hv₀, hσdef, h.ρV_apply] at this
    exact this
  have hfw : h.actV t c.2.2 = c.2.2 := by
    have := hfw₀
    rw [evalV_tupleOf hσG.1 hw₀, fn, dite_eq_left hw₀, hσdef, h.ρV_apply] at this
    exact this
  have hactE : ∀ x, x < 512 → h.actE t x = evalE (bOf u (tupleOf σ)) x := by
    intro x hx
    have := h.eAct_ρV ⟨t, ht⟩ ⟨x, hx⟩
    rw [h.ρE_apply] at this
    exact this.symm
  have hI := h.card_inv_lt ht ht2 hv₀ hw₀ hfv hfw fun x hx hxe => hβ x hx (by
    rw [← hactE x hx]; exact hxe)
  have hcV : Nat.card {v : Fin 64 // h.actV t v = v} = (fixV (tupleOf σ)).length := by
    rw [fixV, card_filter_range]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    rw [beq_iff_eq, evalV_tupleOf hσG.1 v.2, fn, dite_eq_left v.2, hσdef, h.ρV_apply]
  have hcE : Nat.card {e : Fin 512 // h.actE t e = e} =
      ((List.range 512).filter fun e => evalE (bOf u (tupleOf σ)) e == e).length := by
    rw [card_filter_range]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun e => ?_)
    rw [beq_iff_eq, hactE e e.2]
  rw [hcV, hcE] at hI
  set C := (R ⊓ centralizer ({t} : Set G) : Subgroup G) with hCdef
  have hC2 : IsPGroup 2 C := hR2.to_le inf_le_left
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hn : Nat.card Rb = els.length := hRbc
  have key : 2 ^ 15 * els.length < 32 * els.length * Nat.card C := by
    calc 2 ^ 15 * els.length ≤ Nat.card R := by rw [← hn]; exact hRcard
      _ ≤ Nat.card {j : Jh // (t * j) * (t * j) = 1} * Nat.card C := hcount
      _ < (fixV (tupleOf σ)).length *
          ((List.range 512).filter fun e => evalE (bOf u (tupleOf σ)) e == e).length *
            Nat.card C := Nat.mul_lt_mul_of_pos_right hI hCpos
      _ ≤ 32 * els.length * Nat.card C := Nat.mul_le_mul_right _ hfix
  have hC10 : 2 ^ 10 < Nat.card C := by
    have h32 : 0 < 32 * els.length := by omega
    have : 32 * els.length * 2 ^ 10 < 32 * els.length * Nat.card C := by
      calc 32 * els.length * 2 ^ 10 = 2 ^ 15 * els.length := by ring
        _ < 32 * els.length * Nat.card C := key
    exact Nat.lt_of_mul_lt_mul_left this
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hC2
  refine ⟨C, inf_le_right, hC2, ?_⟩
  rw [ha] at hC10 ⊢
  have : 10 < a := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hC10
  exact Nat.pow_le_pow_right (by norm_num) this

theorem exists_big_of_cert {t : G} (htS : t ∈ h.SG) (htJ : t ∉ Jh) (ht2 : t * t = 1)
    (hpres : Pres u (h.ρV ⟨t, h.SG_le_X htS⟩)) :
    ∃ C : Subgroup G, C ≤ centralizer ({t} : Set G) ∧ IsPGroup 2 C ∧ 2 ^ 11 ≤ Nat.card C := by
  have ht : t ∈ normalizer (Jh : Set G) := h.SG_le_X htS
  set σ := h.ρV ⟨t, ht⟩ with hσdef
  have hσG : σ ∈ Gq u := h.ρV_mem_Gq _
  have hσσ : σ * σ = 1 := by
    rw [hσdef, ← map_mul, show (⟨t, ht⟩ : normalizer (Jh : Set G)) * ⟨t, ht⟩ = 1 from
      Subtype.ext ht2, map_one]
  have hσ1 : σ ≠ 1 := fun h1 =>
    htJ ((h.mem_Kk_iff_of_mem_SG htS).1 ⟨⟨t, ht⟩, MonoidHom.mem_ker.2 h1, rfl⟩)
  have hinv : isInvT (tupleOf σ) = true := by
    simp only [isInvT, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    exact ⟨by rw [← tupleOf_mul hσG.1, hσσ, tupleOf_one],
      fun he => hσ1 (eq_one_of_tupleOf_eq_idT hσG he)⟩
  obtain ⟨w, -, k, hk, hconj⟩ := conj_of_mem hσG hinv hpres
  obtain ⟨hvr, c, hc⟩ := killRep_facts u hk
  obtain ⟨ρr, hρr, hρrt⟩ := exists_of_validT hvr
  have hg : evalWG z l₁ l₂ t w ∈ normalizer (Jh : Set G) := h.evalWG_mem ht w
  set g := evalWG z l₁ l₂ t w with hgdef
  set γ := h.ρV ⟨g, hg⟩ with hγdef
  have hγG : γ ∈ Gq u := h.ρV_mem_Gq _
  have hγt : tupleOf γ = evalW (tupleOf σ) w := h.tupleOf_evalWG ht w
  have ht' : g * t * g⁻¹ ∈ normalizer (Jh : Set G) := mul_mem (mul_mem hg ht) (inv_mem hg)
  have ht'2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hρ' : h.ρV ⟨g * t * g⁻¹, ht'⟩ = γ * σ * γ⁻¹ := by
    rw [hγdef, hσdef, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hρr' : ρr = γ * σ * γ⁻¹ := by
    have h1 : ρr * γ = γ * σ := tupleOf_injective (mul_mem hρr hγG).1 (mul_mem hγG hσG).1 (by
      rw [tupleOf_mul hρr.1, tupleOf_mul hγG.1, hρrt, hγt]
      exact hconj.symm)
    rw [← h1]
    group
  obtain ⟨C, hCc, hC2, hCcard⟩ := h.exists_big_of_validCert ht' ht'2 (c := c) (by
    rw [hρ', ← hρr', hρrt]
    exact hc)
  refine ⟨C.map (MulAut.conj g⁻¹).toMonoidHom, ?_, hC2.map _, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxc := mem_centralizer_singleton_iff.1 (hCc hx)
    refine mem_centralizer_singleton_iff.2 ?_
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hxc]
      _ = t * (g⁻¹ * x * g) := by group
  · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hCcard

end Kill

end KillData

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
