module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure IsChiefFactor (Γ W₀ W₁ : Subgroup G) : Prop where
  lt : W₀ < W₁
  norm₀ : Γ ≤ Subgroup.normalizer (W₀ : Set G)
  norm₁ : Γ ≤ Subgroup.normalizer (W₁ : Set G)
  chief : ∀ W : Subgroup G, W₀ ≤ W → W ≤ W₁ → Γ ≤ Subgroup.normalizer (W : Set G) →
    W = W₀ ∨ W = W₁

structure ChiefLin (Γ W₀ W₁ : Subgroup G) (V : Type) [AddCommGroup V] [Module (ZMod 2) V] where
  π : ↥W₁ →* Multiplicative V
  surj : Function.Surjective π
  ker_eq : π.ker = W₀.subgroupOf W₁
  normalizes : Γ ≤ Subgroup.normalizer (W₁ : Set G)
  ρ : ↥Γ →* GLV V
  spec : ∀ (x : ↥Γ) (u v : ↥W₁), (v : G) = x * u * (x : G)⁻¹ →
    Multiplicative.toAdd (π v) = ρ x (Multiplicative.toAdd (π u))

section Existence

variable {Γ W₀ W₁ : Subgroup G}

theorem IsChiefFactor.normal (hc : IsChiefFactor Γ W₀ W₁) (hW₁Γ : W₁ ≤ Γ) :
    (W₀.subgroupOf W₁).Normal :=
  ⟨fun n hn w => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hc.norm₀ (hW₁Γ w.2)) n).mp hn⟩

section Quot

variable [(W₀.subgroupOf W₁).Normal]

private theorem conj_mem_of_le_normalizer {W : Subgroup G} {γ : G}
    (hγ : γ ∈ Subgroup.normalizer (W : Set G)) {w : G} (hw : w ∈ W) : γ * w * γ⁻¹ ∈ W :=
  (Subgroup.mem_normalizer_iff.mp hγ w).mp hw

private def preQ (S : Subgroup (↥W₁ ⧸ W₀.subgroupOf W₁)) : Subgroup G :=
  (S.comap (QuotientGroup.mk' (W₀.subgroupOf W₁))).map W₁.subtype

private theorem mem_preQ {S : Subgroup (↥W₁ ⧸ W₀.subgroupOf W₁)} {g : G} :
    g ∈ preQ S ↔ ∃ h : g ∈ W₁, (QuotientGroup.mk ⟨g, h⟩ : ↥W₁ ⧸ W₀.subgroupOf W₁) ∈ S := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  · rintro ⟨h, hS⟩
    exact ⟨⟨g, h⟩, hS, rfl⟩

private theorem preQ_le (S : Subgroup (↥W₁ ⧸ W₀.subgroupOf W₁)) : preQ S ≤ W₁ := by
  rintro _ ⟨w, -, rfl⟩
  exact w.2

private theorem le_preQ (S : Subgroup (↥W₁ ⧸ W₀.subgroupOf W₁)) (hW : W₀ ≤ W₁) :
    W₀ ≤ preQ S := by
  intro g hg
  refine (mem_preQ).mpr ⟨hW hg, ?_⟩
  rw [(QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hg)]
  exact S.one_mem

private theorem preQ_ne (hW : W₀ ≤ W₁) {S : Subgroup (↥W₁ ⧸ W₀.subgroupOf W₁)} (hS : S ≠ ⊥) :
    preQ S ≠ W₀ := by
  intro h
  apply hS
  refine (Subgroup.eq_bot_iff_forall _).mpr fun s hs => ?_
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
  have hw : (w : G) ∈ preQ S := (mem_preQ).mpr ⟨w.2, hs⟩
  rw [h] at hw
  exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hw)

private theorem eq_top_of_preQ {S : Subgroup (↥W₁ ⧸ W₀.subgroupOf W₁)} (hS : preQ S = W₁) :
    S = ⊤ := by
  refine (Subgroup.eq_top_iff' _).mpr fun s => ?_
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
  have hw : (w : G) ∈ preQ S := by rw [hS]; exact w.2
  obtain ⟨h, hmem⟩ := (mem_preQ).mp hw
  exact hmem

private noncomputable def conjQ (h₀ : W₀ ≤ W₁) (γ : G)
    (hγ₀ : γ ∈ Subgroup.normalizer (W₀ : Set G)) (hγ₁ : γ ∈ Subgroup.normalizer (W₁ : Set G)) :
    ↥W₁ ⧸ W₀.subgroupOf W₁ →* ↥W₁ ⧸ W₀.subgroupOf W₁ :=
  QuotientGroup.map (W₀.subgroupOf W₁) (W₀.subgroupOf W₁)
    { toFun := fun w => ⟨γ * w * γ⁻¹, conj_mem_of_le_normalizer hγ₁ w.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
    (fun w hw => by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact conj_mem_of_le_normalizer hγ₀ (Subgroup.mem_subgroupOf.mp hw))

private theorem conjQ_mk (h₀ : W₀ ≤ W₁) (γ : G)
    (hγ₀ : γ ∈ Subgroup.normalizer (W₀ : Set G)) (hγ₁ : γ ∈ Subgroup.normalizer (W₁ : Set G))
    (w : ↥W₁) :
    conjQ h₀ γ hγ₀ hγ₁ (QuotientGroup.mk w) =
      QuotientGroup.mk ⟨γ * w * γ⁻¹, conj_mem_of_le_normalizer hγ₁ w.2⟩ :=
  rfl

private theorem conjQ_surjective (h₀ : W₀ ≤ W₁) (γ : G)
    (hγ₀ : γ ∈ Subgroup.normalizer (W₀ : Set G)) (hγ₁ : γ ∈ Subgroup.normalizer (W₁ : Set G)) :
    Function.Surjective (conjQ h₀ γ hγ₀ hγ₁) := by
  intro s
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
  have hinv₁ : γ⁻¹ ∈ Subgroup.normalizer (W₁ : Set G) := inv_mem hγ₁
  refine ⟨QuotientGroup.mk ⟨γ⁻¹ * w * γ⁻¹⁻¹, conj_mem_of_le_normalizer hinv₁ w.2⟩, ?_⟩
  rw [conjQ_mk]
  congr 1
  ext
  simp [mul_assoc]

private theorem le_normalizer_preQ (hc : IsChiefFactor Γ W₀ W₁)
    {S : Subgroup (↥W₁ ⧸ W₀.subgroupOf W₁)}
    (hS : ∀ γ (hγ : γ ∈ Γ) (s : ↥W₁ ⧸ W₀.subgroupOf W₁), s ∈ S →
      conjQ hc.lt.le γ (hc.norm₀ hγ) (hc.norm₁ hγ) s ∈ S) :
    Γ ≤ Subgroup.normalizer (preQ S : Set G) := by
  intro γ hγ
  have key : ∀ γ ∈ Γ, ∀ g ∈ preQ S, γ * g * γ⁻¹ ∈ preQ S := by
    intro γ hγ g hg
    obtain ⟨hgW, hgS⟩ := (mem_preQ).mp hg
    refine (mem_preQ).mpr ⟨conj_mem_of_le_normalizer (hc.norm₁ hγ) hgW, ?_⟩
    have := hS γ hγ _ hgS
    rwa [conjQ_mk] at this
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key γ hγ g, fun h => ?_⟩
  have := key γ⁻¹ (inv_mem hγ) _ h
  simpa [mul_assoc] using this

private theorem conjQ_mem_center (hc : IsChiefFactor Γ W₀ W₁) {γ : G} (hγ : γ ∈ Γ)
    {s : ↥W₁ ⧸ W₀.subgroupOf W₁} (hs : s ∈ Subgroup.center (↥W₁ ⧸ W₀.subgroupOf W₁)) :
    conjQ hc.lt.le γ (hc.norm₀ hγ) (hc.norm₁ hγ) s ∈
      Subgroup.center (↥W₁ ⧸ W₀.subgroupOf W₁) := by
  rw [Subgroup.mem_center_iff] at hs ⊢
  intro t
  obtain ⟨t', rfl⟩ := conjQ_surjective hc.lt.le γ (hc.norm₀ hγ) (hc.norm₁ hγ) t
  rw [← map_mul, ← map_mul, hs t']

private theorem mul_comm_quot (hc : IsChiefFactor Γ W₀ W₁) (hW₁ : IsPGroup 2 W₁) :
    ∀ a b : ↥W₁ ⧸ W₀.subgroupOf W₁, a * b = b * a := by
  have hp : IsPGroup 2 (↥W₁ ⧸ W₀.subgroupOf W₁) := hW₁.to_quotient _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial (↥W₁ ⧸ W₀.subgroupOf W₁) := by
    obtain ⟨w, hw₁, hw₀⟩ := SetLike.exists_of_lt hc.lt
    refine ⟨⟨QuotientGroup.mk ⟨w, hw₁⟩, 1, fun h => hw₀ ?_⟩⟩
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h)
  have hZ : Subgroup.center (↥W₁ ⧸ W₀.subgroupOf W₁) ≠ ⊥ := by
    have := hp.center_nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this
  rcases hc.chief _ (le_preQ _ hc.lt.le) (preQ_le _)
      (le_normalizer_preQ hc fun γ hγ s hs => conjQ_mem_center hc hγ hs) with h | h
  · exact absurd h (preQ_ne hc.lt.le hZ)
  · have htop := eq_top_of_preQ h
    intro a b
    have ha : a ∈ Subgroup.center (↥W₁ ⧸ W₀.subgroupOf W₁) := htop ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm

private theorem mul_self_quot (hc : IsChiefFactor Γ W₀ W₁) (hW₁ : IsPGroup 2 W₁) :
    ∀ a : ↥W₁ ⧸ W₀.subgroupOf W₁, a * a = 1 := by
  have hcomm := mul_comm_quot hc hW₁
  letI : CommGroup (↥W₁ ⧸ W₀.subgroupOf W₁) :=
    { (inferInstance : Group (↥W₁ ⧸ W₀.subgroupOf W₁)) with mul_comm := hcomm }
  let E : Subgroup (↥W₁ ⧸ W₀.subgroupOf W₁) := (powMonoidHom 2 :
    (↥W₁ ⧸ W₀.subgroupOf W₁) →* (↥W₁ ⧸ W₀.subgroupOf W₁)).ker
  have hE : ∀ s, s ∈ E ↔ s * s = 1 := fun s => by
    show s ^ 2 = 1 ↔ s * s = 1
    rw [pow_two]
  have hp : IsPGroup 2 (↥W₁ ⧸ W₀.subgroupOf W₁) := hW₁.to_quotient _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : E ≠ ⊥ := by
    obtain ⟨w, hw₁, hw₀⟩ := SetLike.exists_of_lt hc.lt
    have hne1 : (QuotientGroup.mk ⟨w, hw₁⟩ : ↥W₁ ⧸ W₀.subgroupOf W₁) ≠ 1 := fun h =>
      hw₀ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h))
    obtain ⟨k, hk⟩ := hp (QuotientGroup.mk ⟨w, hw₁⟩)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne1 (by simpa using hk)
    have h2 : (2 : ℕ) ∣ Nat.card (↥W₁ ⧸ W₀.subgroupOf W₁) := by
      have hord : orderOf (QuotientGroup.mk ⟨w, hw₁⟩ : ↥W₁ ⧸ W₀.subgroupOf W₁) ∣ 2 ^ k :=
        orderOf_dvd_of_pow_eq_one hk
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
      have hj0 : j ≠ 0 := by
        rintro rfl
        exact hne1 (orderOf_eq_one_iff.mp (by simpa using hj))
      have h2o : 2 ∣ orderOf (QuotientGroup.mk ⟨w, hw₁⟩ : ↥W₁ ⧸ W₀.subgroupOf W₁) := by
        rw [hj]
        exact dvd_pow_self 2 hj0
      exact h2o.trans (orderOf_dvd_natCard _)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    intro hbot
    have hxE : x ∈ E := (hE x).mpr (by rw [← pow_two, ← hx, pow_orderOf_eq_one])
    rw [hbot, Subgroup.mem_bot] at hxE
    rw [hxE, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hconjE : ∀ γ (hγ : γ ∈ Γ) (s : ↥W₁ ⧸ W₀.subgroupOf W₁), s ∈ E →
      conjQ hc.lt.le γ (hc.norm₀ hγ) (hc.norm₁ hγ) s ∈ E := by
    intro γ hγ s hs
    rw [hE] at hs ⊢
    rw [← map_mul, hs, map_one]
  rcases hc.chief _ (le_preQ _ hc.lt.le) (preQ_le _) (le_normalizer_preQ hc hconjE) with h | h
  · exact absurd h (preQ_ne hc.lt.le hne)
  · have htop := eq_top_of_preQ h
    intro a
    exact (hE a).mp (htop ▸ Subgroup.mem_top a)

end Quot

theorem exists_chiefLin (hc : IsChiefFactor Γ W₀ W₁) (hW₁ : IsPGroup 2 W₁) (hW₁Γ : W₁ ≤ Γ) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V) (_ : Finite V),
      Nonempty (ChiefLin Γ W₀ W₁ V) := by
  classical
  haveI := hc.normal hW₁Γ
  set N : Subgroup ↥W₁ := W₀.subgroupOf W₁ with hN
  have hcomm := mul_comm_quot hc hW₁
  have hsq := mul_self_quot hc hW₁
  letI : CommGroup (↥W₁ ⧸ N) := { (inferInstance : Group (↥W₁ ⧸ N)) with mul_comm := hcomm }
  have h2 : ∀ x : Additive (↥W₁ ⧸ N), (2 : ℕ) • x = 0 := by
    intro x
    rw [two_nsmul]
    exact congrArg Additive.ofMul (hsq (Additive.toMul x))
  letI : Module (ZMod 2) (Additive (↥W₁ ⧸ N)) := AddCommGroup.zmodModule h2
  have hconj : ∀ (x : ↥Γ) (u : G), u ∈ W₁ → (x : G) * u * (x : G)⁻¹ ∈ W₁ :=
    fun x u hu => conj_mem_of_le_normalizer (hc.norm₁ x.2) hu
  have hconj₀ : ∀ (x : ↥Γ) (u : G), u ∈ W₀ → (x : G) * u * (x : G)⁻¹ ∈ W₀ :=
    fun x u hu => conj_mem_of_le_normalizer (hc.norm₀ x.2) hu
  let c : ↥Γ → (↥W₁ →* ↥W₁) := fun x =>
    { toFun := fun u => ⟨(x : G) * u * (x : G)⁻¹, hconj x u u.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hc' : ∀ (x : ↥Γ) (u : ↥W₁), ((c x u : ↥W₁) : G) = (x : G) * u * (x : G)⁻¹ :=
    fun _ _ => rfl
  let f : ↥Γ → (↥W₁ ⧸ N →* ↥W₁ ⧸ N) := fun x =>
    QuotientGroup.map N N (c x) (fun u hu => by
      rw [Subgroup.mem_comap, hN, Subgroup.mem_subgroupOf, hc']
      exact hconj₀ x u (Subgroup.mem_subgroupOf.mp hu))
  let a : ↥Γ → (Additive (↥W₁ ⧸ N) →+ Additive (↥W₁ ⧸ N)) := fun x =>
    MonoidHom.toAdditive (f x)
  have ha : ∀ (x : ↥Γ) (u : ↥W₁),
      a x (Additive.ofMul (QuotientGroup.mk u)) = Additive.ofMul (QuotientGroup.mk (c x u)) :=
    fun _ _ => rfl
  have hsurj : ∀ v : Additive (↥W₁ ⧸ N), ∃ u : ↥W₁,
      v = Additive.ofMul (QuotientGroup.mk u) := fun v => by
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    exact ⟨u, by rw [hu]; rfl⟩
  let φ : ↥Γ →* Module.End (ZMod 2) (Additive (↥W₁ ⧸ N)) :=
    { toFun := fun x => (a x).toZModLinearMap 2
      map_one' := by
        refine LinearMap.ext fun v => ?_
        obtain ⟨u, rfl⟩ := hsurj v
        have h1 : c 1 u = u := Subtype.ext (by simp [hc'])
        show a 1 _ = _
        rw [ha, h1]
        rfl
      map_mul' := fun x y => by
        refine LinearMap.ext fun v => ?_
        obtain ⟨u, rfl⟩ := hsurj v
        have h1 : c (x * y) u = c x (c y u) := Subtype.ext (by simp [hc', mul_assoc])
        show a (x * y) _ = a x (a y _)
        rw [ha, ha, ha, h1] }
  let ρ : ↥Γ →* GLV (Additive (↥W₁ ⧸ N)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
      (Additive (↥W₁ ⧸ N))).toMonoidHom.comp φ.toHomUnits
  have hρ : ∀ (x : ↥Γ) (v : Additive (↥W₁ ⧸ N)), ρ x v = φ x v := fun _ _ => rfl
  let π : ↥W₁ →* Multiplicative (Additive (↥W₁ ⧸ N)) :=
    { toFun := fun u => Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk u))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hπ : ∀ u : ↥W₁,
      π u = Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk u : ↥W₁ ⧸ N)) :=
    fun _ => rfl
  refine ⟨Additive (↥W₁ ⧸ N), inferInstance, inferInstance, inferInstance, ⟨{
    π := π
    surj := ?_
    ker_eq := ?_
    normalizes := hc.norm₁
    ρ := ρ
    spec := ?_ }⟩⟩
  · intro w
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul (Multiplicative.toAdd w))
    exact ⟨u, by rw [hπ, hu]; rfl⟩
  · ext u
    rw [MonoidHom.mem_ker, hπ]
    exact QuotientGroup.eq_one_iff u
  · intro x u v huv
    rw [hπ, hπ, hρ]
    have h1 : c x u = v := Subtype.ext huv.symm
    show Additive.ofMul (QuotientGroup.mk v : ↥W₁ ⧸ N) =
      a x (Additive.ofMul (QuotientGroup.mk u))
    rw [ha, h1]

end Existence

namespace ChiefLin

variable {Γ W₀ W₁ : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  (lin : ChiefLin Γ W₀ W₁ V)

@[expose] def img (A : Subgroup G) : Subgroup (GLV V) :=
  (A.subgroupOf Γ).map lin.ρ

@[expose] def vec (u : ↥W₁) : V :=
  Multiplicative.toAdd (lin.π u)

theorem vec_mul (u v : ↥W₁) : lin.vec (u * v) = lin.vec u + lin.vec v := by
  simp [vec]

theorem vec_one : lin.vec 1 = 0 := by
  simp [vec]

theorem vec_inv (u : ↥W₁) : lin.vec u⁻¹ = - lin.vec u := by
  simp [vec]

theorem vec_eq_zero_iff (u : ↥W₁) : lin.vec u = 0 ↔ (u : G) ∈ W₀ := by
  rw [← Subgroup.mem_subgroupOf, ← lin.ker_eq, MonoidHom.mem_ker]
  simp [vec]

theorem vec_surjective : Function.Surjective lin.vec := fun v => by
  obtain ⟨u, hu⟩ := lin.surj (Multiplicative.ofAdd v)
  exact ⟨u, by simp [vec, hu]⟩

theorem ρ_vec (x : ↥Γ) (u v : ↥W₁) (h : (v : G) = x * u * (x : G)⁻¹) :
    lin.ρ x (lin.vec u) = lin.vec v :=
  (lin.spec x u v h).symm

theorem vec_eq_vec_iff (u v : ↥W₁) :
    lin.vec u = lin.vec v ↔ (u : G) * (v : G)⁻¹ ∈ W₀ := by
  have h : lin.vec (u * v⁻¹) = lin.vec u - lin.vec v := by
    rw [lin.vec_mul, lin.vec_inv, sub_eq_add_neg]
  rw [← sub_eq_zero, ← h, lin.vec_eq_zero_iff]
  rfl

theorem ρ_eq_one_iff (x : ↥Γ) :
    lin.ρ x = 1 ↔ ∀ w ∈ W₁, (x : G) * w * (x : G)⁻¹ * w⁻¹ ∈ W₀ := by
  have hconj : ∀ w : G, w ∈ W₁ → (x : G) * w * (x : G)⁻¹ ∈ W₁ := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp (lin.normalizes x.2) w).mp hw
  constructor
  · intro h w hw
    have h1 := lin.ρ_vec x ⟨w, hw⟩ ⟨(x : G) * w * (x : G)⁻¹, hconj w hw⟩ rfl
    rw [h, LinearEquiv.coe_one, id_eq] at h1
    exact (lin.vec_eq_vec_iff ⟨(x : G) * w * (x : G)⁻¹, hconj w hw⟩ ⟨w, hw⟩).mp h1.symm
  · intro h
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨u, rfl⟩ := lin.vec_surjective v
    rw [lin.ρ_vec x u ⟨(x : G) * u * (x : G)⁻¹, hconj u u.2⟩ rfl, LinearEquiv.coe_one, id_eq]
    exact (lin.vec_eq_vec_iff ⟨(x : G) * u * (x : G)⁻¹, hconj u u.2⟩ u).mpr (h u u.2)

include lin in
theorem nontrivial (hlt : W₀ < W₁) : Nontrivial V := by
  obtain ⟨g, hg₁, hg₀⟩ := SetLike.exists_of_lt hlt
  exact ⟨⟨lin.vec ⟨g, hg₁⟩, 0, fun h => hg₀ ((lin.vec_eq_zero_iff ⟨g, hg₁⟩).mp h)⟩⟩

@[expose] def preW (S : Submodule (ZMod 2) V) : Subgroup G :=
  (AddSubgroup.toSubgroup S.toAddSubgroup |>.comap lin.π).map W₁.subtype

theorem mem_preW {S : Submodule (ZMod 2) V} {g : G} :
    g ∈ lin.preW S ↔ ∃ h : g ∈ W₁, lin.vec ⟨g, h⟩ ∈ S := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.2, hu⟩
  · rintro ⟨h, hv⟩
    exact ⟨⟨g, h⟩, hv, rfl⟩

theorem preW_le (S : Submodule (ZMod 2) V) : lin.preW S ≤ W₁ := by
  rintro _ ⟨u, -, rfl⟩
  exact u.2

theorem le_preW (hW : W₀ ≤ W₁) (S : Submodule (ZMod 2) V) : W₀ ≤ lin.preW S := fun g hg =>
  (lin.mem_preW).mpr ⟨hW hg, by
    rw [(lin.vec_eq_zero_iff ⟨g, hW hg⟩).mpr hg]; exact S.zero_mem⟩

theorem le_normalizer_preW {A : Subgroup G} (hAΓ : A ≤ Γ) {S : Submodule (ZMod 2) V}
    (hS : Invariant (lin.img A) S) : A ≤ Subgroup.normalizer (lin.preW S : Set G) := by
  have key : ∀ j ∈ A, ∀ g ∈ lin.preW S, j * g * j⁻¹ ∈ lin.preW S := by
    intro j hj g hg
    obtain ⟨hgW, hv⟩ := (lin.mem_preW).mp hg
    have hconj : j * g * j⁻¹ ∈ W₁ :=
      (Subgroup.mem_normalizer_iff.mp (lin.normalizes (hAΓ hj)) g).mp hgW
    refine (lin.mem_preW).mpr ⟨hconj, ?_⟩
    have h := lin.ρ_vec ⟨j, hAΓ hj⟩ ⟨g, hgW⟩ ⟨j * g * j⁻¹, hconj⟩ rfl
    rw [← h]
    exact hS _ ⟨⟨j, hAΓ hj⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩ _ hv
  intro j hj
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key j hj g, fun h => ?_⟩
  have := key j⁻¹ (inv_mem hj) _ h
  simpa [mul_assoc] using this

theorem isIrr_img (hc : IsChiefFactor Γ W₀ W₁) : IsIrr (lin.img Γ) ⊤ := by
  haveI := lin.nontrivial hc.lt
  unfold IsIrr IrrSec
  refine ⟨fun _ _ _ _ => Submodule.mem_top, bot_lt_top, ?_⟩
  intro S hS _ _
  rcases hc.chief (lin.preW S) (lin.le_preW hc.lt.le S) (lin.preW_le S)
      (lin.le_normalizer_preW le_rfl hS) with h | h
  · left
    refine (Submodule.eq_bot_iff _).mpr fun y hy => ?_
    obtain ⟨u, rfl⟩ := lin.vec_surjective y
    have hu : (u : G) ∈ lin.preW S := (lin.mem_preW).mpr ⟨u.2, hy⟩
    rw [h] at hu
    exact (lin.vec_eq_zero_iff u).mpr hu
  · right
    refine (Submodule.eq_top_iff').mpr fun y => ?_
    obtain ⟨u, rfl⟩ := lin.vec_surjective y
    have hu : (u : G) ∈ lin.preW S := by rw [h]; exact u.2
    obtain ⟨_, hv⟩ := (lin.mem_preW).mp hu
    exact hv

theorem ρ_eq_one_of_normal [Finite V] (hc : IsChiefFactor Γ W₀ W₁) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hΓP : Γ ≤ Subgroup.normalizer (P : Set G)) (x : ↥Γ)
    (hx : (x : G) ∈ P) : lin.ρ x = 1 := by
  haveI := lin.nontrivial hc.lt
  set F := fixedSpace (lin.img P) with hFdef
  have hF : Invariant (lin.img Γ) F := by
    rintro _ ⟨γ, -, rfl⟩ v hv k hk
    obtain ⟨p, hp, rfl⟩ := hk
    have hp' : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
    have hconj : (γ⁻¹ * p * γ : ↥Γ) ∈ P.subgroupOf Γ := by
      rw [Subgroup.mem_subgroupOf]
      have := (Subgroup.mem_normalizer_iff.mp (hΓP (inv_mem γ.2)) p).mp hp'
      simpa [mul_assoc] using this
    have h1 : lin.ρ (γ⁻¹ * p * γ) v = v := hv _ ⟨_, hconj, rfl⟩
    have h2 : lin.ρ p (lin.ρ γ v) = lin.ρ γ (lin.ρ (γ⁻¹ * p * γ) v) := by
      rw [map_mul, map_mul, map_inv]
      simp [LinearEquiv.mul_apply]
    rw [h2, h1]
  rcases hc.chief (lin.preW F) (lin.le_preW hc.lt.le F) (lin.preW_le F)
      (lin.le_normalizer_preW le_rfl hF) with h | h
  · exfalso
    have hPimg : IsPGroup 2 ↥(lin.img P) :=
      (hP.comap_of_injective Γ.subtype Subtype.val_injective).map lin.ρ
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
    have h2V : 2 ∣ Nat.card V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
      exact dvd_pow_self 2 (Module.finrank_pos (R := ZMod 2) (M := V)).ne'
    have h0 : (0 : V) ∈ MulAction.fixedPoints ↥(lin.img P) V := fun g => by
      show (g : GLV V) 0 = 0
      exact map_zero _
    obtain ⟨b, hb, hb0⟩ := hPimg.exists_fixed_point_of_prime_dvd_card_of_fixed_point V h2V h0
    have hbF : b ∈ F := fun k hk => hb ⟨k, hk⟩
    obtain ⟨u, rfl⟩ := lin.vec_surjective b
    have hu : (u : G) ∈ lin.preW F := (lin.mem_preW).mpr ⟨u.2, hbF⟩
    rw [h] at hu
    exact hb0 ((lin.vec_eq_zero_iff u).mpr hu).symm
  · refine LinearEquiv.ext fun v => ?_
    obtain ⟨u, rfl⟩ := lin.vec_surjective v
    have hu : (u : G) ∈ lin.preW F := by rw [h]; exact u.2
    obtain ⟨_, hv⟩ := (lin.mem_preW).mp hu
    exact hv (lin.ρ x) ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

end ChiefLin

end CFSG.CGT.Foote82
