module

public import CFSG.LocalAnalysis.GH72.PGammaL2Local
public import CFSG.GroupTheory.CentralSylowComplement
public import CFSG.GroupTheory.GroupAction.CoprimeFiniteSubgroups
public import CFSG.GroupTheory.ThompsonAxB
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerAction

public section

namespace CFSG.GH72

open Subgroup
open scoped Pointwise MatrixGroups commutatorElement
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.GorensteinWalter (PGL2 IsOddPrimePower)

local notation "A₇" => alternatingGroup (Fin 7)

section General

variable {X : Type*} [Group X]

theorem le_normalizer_sup_of_le_normalizer {H K M : Subgroup X}
    (hH : M ≤ normalizer (H : Set X)) (hK : M ≤ normalizer (K : Set X)) :
    M ≤ normalizer ((H ⊔ K : Subgroup X) : Set X) := fun g hg => by
  have hA := hH hg
  have hB := hK hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem le_normalizer_inf_of_le_normalizer {H K M : Subgroup X}
    (hH : M ≤ normalizer (H : Set X)) (hK : M ≤ normalizer (K : Set X)) :
    M ≤ normalizer ((H ⊓ K : Subgroup X) : Set X) := fun _ hg =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨hH hg, hK hg⟩

theorem normalizer_inf_centralizer_le_normalizer_inf {L : Subgroup X} {v : X} :
    normalizer (L : Set X) ⊓ centralizer ({v} : Set X) ≤
      normalizer ((L ⊓ centralizer ({v} : Set X) : Subgroup X) : Set X) :=
  le_normalizer_inf_of_le_normalizer inf_le_left (inf_le_right.trans le_normalizer)

theorem normalizer_le_normalizer_of_forall_le [Finite X] {p : ℕ} {S C : Subgroup X}
    (hSC : S ≤ C) (hS : IsPGroup p S)
    (hall : ∀ R : Subgroup X, R ≤ C → IsPGroup p R → R ≤ S) :
    normalizer (C : Set X) ≤ normalizer (S : Set X) := fun g hg => by
  apply mem_normalizer_fintype
  intro y hy
  have hle : S.map (MulAut.conj g).toMonoidHom ≤ C := by
    rintro _ ⟨z, hz, rfl⟩
    exact (mem_normalizer_iff.mp hg z).mp (hSC hz)
  exact hall _ hle (hS.map _) ⟨y, hy, rfl⟩

theorem orderOf_dvd_orderOf_mul_of_mem_centralizer {L : Subgroup X}
    (hZ : L ⊓ centralizer (L : Set X) = ⊥) {l c : X} (hl : l ∈ L)
    (hc : c ∈ centralizer (L : Set X)) : orderOf l ∣ orderOf (l * c) := by
  have hlc : Commute l c := mem_centralizer_iff.mp hc l hl
  apply orderOf_dvd_of_pow_eq_one
  have h1 : l ^ orderOf (l * c) * c ^ orderOf (l * c) = 1 := by
    rw [← hlc.mul_pow, pow_orderOf_eq_one]
  have h2 : l ^ orderOf (l * c) = (c ^ orderOf (l * c))⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : l ^ orderOf (l * c) ∈ L ⊓ centralizer (L : Set X) :=
    ⟨L.pow_mem hl _, h2 ▸ (centralizer _).inv_mem ((centralizer _).pow_mem hc _)⟩
  rw [hZ, mem_bot] at h3
  exact h3

theorem commutatorElement_mem_inf_of_mem_normalizer {W M : Subgroup X} (hM : M.Normal) {w a : X}
    (hw : w ∈ W) (ha : a ∈ M) (haW : a ∈ normalizer (W : Set X)) : ⁅w, a⁆ ∈ W ⊓ M := by
  rw [commutatorElement_def]
  refine ⟨?_, ?_⟩
  · have h : a * w⁻¹ * a⁻¹ ∈ W := (mem_normalizer_iff.mp haW _).mp (W.inv_mem hw)
    have := W.mul_mem hw h
    rwa [← mul_assoc, ← mul_assoc] at this
  · exact M.mul_mem (hM.conj_mem a ha w) (M.inv_mem ha)

theorem commutator_sup_le_sup_inf {L L₁ Z V W : Subgroup X} (hL : L.Normal) (hL₁ : L₁.Normal)
    (hVL : V ≤ L) (hZL₁ : Z ≤ L₁) (hZV : Z ≤ normalizer (V : Set X))
    (hW : Z ⊔ V ≤ normalizer (W : Set X)) : ⁅W, Z ⊔ V⁆ ≤ W ⊓ L₁ ⊔ W ⊓ L := by
  rw [Subgroup.commutator_le]
  intro w hw a ha
  have ha' : a ∈ (Z : Set X) * V := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right Z V hZV]
    exact ha
  obtain ⟨z, hz, u, hu, rfl⟩ := ha'
  have hzW : z ∈ normalizer (W : Set X) := hW (mem_sup_left hz)
  have huW : u ∈ normalizer (W : Set X) := hW (mem_sup_right hu)
  have h1 : ⁅w, z⁆ ∈ W ⊓ L₁ := commutatorElement_mem_inf_of_mem_normalizer hL₁ hw (hZL₁ hz) hzW
  have h2 : ⁅w, u⁆ ∈ W ⊓ L := commutatorElement_mem_inf_of_mem_normalizer hL hw (hVL hu) huW
  have h3 : z * ⁅w, u⁆ * z⁻¹ ∈ W ⊓ L :=
    ⟨(mem_normalizer_iff.mp hzW _).mp h2.1, hL.conj_mem _ h2.2 z⟩
  have h4 : ⁅w, z * u⁆ = ⁅w, z⁆ * (z * ⁅w, u⁆ * z⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [h4]
  exact mul_mem_sup h1 h3

theorem le_commutator_sup_inf_centralizer_of_isPGroup [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {A W : Subgroup X} (hA : IsPGroup 2 A) (hW : IsPGroup p W)
    (hAW : A ≤ normalizer (W : Set X)) : W ≤ ⁅W, A⁆ ⊔ W ⊓ centralizer (A : Set X) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hA.exists_card_eq
  obtain ⟨n, hn⟩ := hW.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (Nat.card W) := by
    rw [hm, hn]
    exact Nat.Coprime.pow m n ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have : Group.IsNilpotent W := hW.isNilpotent
  exact CFSG.GroupTheory.le_commutator_sup_inf_centralizer_of_coprime_of_finite hAW hcop
    inferInstance

theorem exists_isMaxInvIn_le [Finite X] {p : ℕ} {A H Q : Subgroup X} (hQH : Q ≤ H)
    (hQ : IsPGroup p Q) (hAQ : A ≤ normalizer (Q : Set X)) :
    ∃ P : Subgroup X, IsMaxInvIn p A H P ∧ Q ≤ P := by
  classical
  have : Finite (Subgroup X) :=
    Finite.of_injective (fun K : Subgroup X => (K : Set X)) SetLike.coe_injective
  let S : Set (Subgroup X) := {R | R ≤ H ∧ IsPGroup p R ∧ A ≤ normalizer (R : Set X) ∧ Q ≤ R}
  have hne : (Set.toFinite S).toFinset.Nonempty :=
    ⟨Q, (Set.toFinite S).mem_toFinset.mpr ⟨hQH, hQ, hAQ, le_rfl⟩⟩
  obtain ⟨P, hPS, hPmax⟩ := (Set.toFinite S).toFinset.exists_max_image (fun R => Nat.card R) hne
  rw [Set.Finite.mem_toFinset] at hPS
  obtain ⟨hPH, hPp, hAP, hQP⟩ := hPS
  refine ⟨P, ⟨hPH, hPp, hAP, fun R hRH hRp hAR hPR => ?_⟩, hQP⟩
  have hcard := hPmax R ((Set.toFinite S).mem_toFinset.mpr ⟨hRH, hRp, hAR, hQP.trans hPR⟩)
  exact (Subgroup.eq_of_le_of_card_ge hPR hcard).symm

theorem odd_card_sup_of_mul_comm [Finite X] {F P : Subgroup X}
    (hFP : (F : Set X) * P = P * F) (hcop : Nat.Coprime (Nat.card F) (Nat.card P))
    (hF : Odd (Nat.card F)) (hP : Odd (Nat.card P)) : Odd (Nat.card (F ⊔ P : Subgroup X)) := by
  let Y : Subgroup X :=
    { carrier := (F : Set X) * P
      one_mem' := ⟨1, F.one_mem, 1, P.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨f₁, hf₁, p₁, hp₁, rfl⟩ ⟨f₂, hf₂, p₂, hp₂, rfl⟩
        have h : p₁ * f₂ ∈ (P : Set X) * F := ⟨p₁, hp₁, f₂, hf₂, rfl⟩
        rw [← hFP] at h
        obtain ⟨f₃, hf₃, p₃, hp₃, h3⟩ := h
        have h3' : f₃ * p₃ = p₁ * f₂ := h3
        refine ⟨f₁ * f₃, F.mul_mem hf₁ hf₃, p₃ * p₂, P.mul_mem hp₃ hp₂, ?_⟩
        calc f₁ * f₃ * (p₃ * p₂) = f₁ * (f₃ * p₃) * p₂ := by group
          _ = f₁ * p₁ * (f₂ * p₂) := by rw [h3']; group
      inv_mem' := by
        rintro _ ⟨f, hf, q, hq, rfl⟩
        have h : q⁻¹ * f⁻¹ ∈ (P : Set X) * F := ⟨q⁻¹, P.inv_mem hq, f⁻¹, F.inv_mem hf, rfl⟩
        rw [← hFP] at h
        rw [mul_inv_rev]
        exact h }
  have hY : F ⊔ P = Y := le_antisymm
    (sup_le (fun f hf => ⟨f, hf, 1, P.one_mem, mul_one f⟩)
      (fun q hq => ⟨1, F.one_mem, q, hq, one_mul q⟩))
    (by rintro _ ⟨f, hf, q, hq, rfl⟩; exact mul_mem_sup hf hq)
  have hle : Nat.card Y ≤ Nat.card F * Nat.card P := by
    have hsurj : Function.Surjective
        (fun x : F × P => (⟨x.1 * x.2, x.1, x.1.2, x.2, x.2.2, rfl⟩ : Y)) := by
      rintro ⟨_, f, hf, q, hq, rfl⟩
      exact ⟨(⟨f, hf⟩, ⟨q, hq⟩), rfl⟩
    calc Nat.card Y ≤ Nat.card (F × P) := Nat.card_le_card_of_surjective _ hsurj
      _ = Nat.card F * Nat.card P := Nat.card_prod _ _
  have hdvd : Nat.card F * Nat.card P ∣ Nat.card Y := by
    rw [← hY]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop (card_dvd_of_le le_sup_left)
      (card_dvd_of_le le_sup_right)
  have heq : Nat.card Y = Nat.card F * Nat.card P :=
    le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdvd)
  rw [hY, heq]
  exact hF.mul hP

theorem le_centralizer_of_thompson_AxB [Finite X] {p : ℕ} [Fact p.Prime] {P R B : Subgroup X}
    (hP : IsPGroup p P) (hR : Nat.Coprime (Nat.card R) p) (hB : IsPGroup p B)
    (hRP : R ≤ normalizer (P : Set X)) (hBP : B ≤ normalizer (P : Set X)) (hRB : ⁅R, B⁆ = ⊥)
    (hfix : P ⊓ centralizer (B : Set X) ≤ centralizer (R : Set X)) :
    P ≤ centralizer (R : Set X) := by
  have hRB' : R ≤ centralizer (B : Set X) := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hRB
  let α : R →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hRP)
  let β : B →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hBP)
  have hα : ∀ (r : R) (x : P), ((α r x : P) : X) = r * x * (r : X)⁻¹ := fun r x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe P (Subgroup.inclusion hRP r) x
  have hβ : ∀ (b : B) (x : P), ((β b x : P) : X) = b * x * (b : X)⁻¹ := fun b x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe P (Subgroup.inclusion hBP b) x
  have hcomm : ∀ r b, α r * β b = β b * α r := by
    intro r b
    refine MulEquiv.ext fun x => Subtype.ext ?_
    have hrb : (b : X) * r = r * b := mem_centralizer_iff.mp (hRB' r.2) b b.2
    rw [MulAut.mul_apply, MulAut.mul_apply, hα, hβ, hβ, hα]
    calc (r : X) * (b * x * (b : X)⁻¹) * (r : X)⁻¹ = (r * b) * x * ((r : X) * b)⁻¹ := by group
      _ = (b * r) * x * ((b : X) * r)⁻¹ := by rw [hrb]
      _ = b * (r * x * (r : X)⁻¹) * (b : X)⁻¹ := by group
  have hfix' : ∀ r x, (∀ b, β b x = x) → α r x = x := by
    intro r x hx
    have hxB : (x : X) ∈ centralizer (B : Set X) := by
      rw [mem_centralizer_iff]
      intro b hb
      have h := congrArg Subtype.val (hx ⟨b, hb⟩)
      rw [hβ] at h
      calc b * (x : X) = b * x * b⁻¹ * b := by group
        _ = x * b := by rw [h]
    have hrx : (r : X) * x = x * r := mem_centralizer_iff.mp (hfix ⟨x.2, hxB⟩) r r.2
    apply Subtype.ext
    rw [hα, hrx, mul_inv_cancel_right]
  have hR' : ¬ p ∣ Nat.card R :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hR.symm
  have key := CFSG.GroupTheory.thompson_A_times_B hP hR' hB α β hcomm hfix'
  intro x hx
  rw [mem_centralizer_iff]
  intro r hr
  have h := congrArg (fun f : MulAut P => ((f ⟨x, hx⟩ : P) : X)) (key ⟨r, hr⟩)
  simp only [hα, MulAut.one_apply] at h
  calc r * x = r * x * r⁻¹ * r := by group
    _ = x * r := by rw [h]

theorem mem_centralizer_sup_of_mem {Z V : Subgroup X} {x : X}
    (hZ : x ∈ centralizer (Z : Set X)) (hV : x ∈ centralizer (V : Set X)) :
    x ∈ centralizer ((Z ⊔ V : Subgroup X) : Set X) := by
  rw [mem_centralizer_iff]
  intro a ha
  have hle : Z ⊔ V ≤ centralizer ({x} : Set X) := sup_le
    (fun z hz => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hZ z hz))
    (fun v hv => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hV v hv))
  exact mem_centralizer_singleton_iff.mp (hle ha)

end General

section Commutation

variable {X : Type*} [Group X]

theorem commutatorElement_mem_centralizer_of_aSeven [Finite X] {L Z : Subgroup X} (hL : L.Normal)
    (e : L ≃* A₇) (hZ : IsKleinFour Z) (hZL : Z ≤ L) {x y : X}
    (hxZ : x ∈ centralizer (Z : Set X)) (hyZ : y ∈ centralizer (Z : Set X))
    (hxo : Odd (orderOf x)) (hyo : Odd (orderOf y)) : ⁅x, y⁆ ∈ centralizer (L : Set X) := by
  have := hL
  have hLC : L ⊓ centralizer (L : Set X) = ⊥ :=
    inf_centralizer_eq_bot_of_isL2OrA7 L (qmin := 5) (Or.inl ⟨e⟩)
  obtain ⟨z, hz, hz1, -⟩ := exists_mem_kleinFour_ne hZ (one_mem Z)
  have hz2 : orderOf z = 2 := orderOf_eq_prime (sq_eq_one_of_mem_kleinFour hZ hz) hz1
  obtain ⟨U, -, hUc, hodd⟩ := exists_card_eq_three_forall_odd_mem_of_aSeven e (hZL hz) hz2
  have hUcyc : IsCyclic U := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card hUc
  let φ : X →* MulAut L := MulAut.conjNormal
  have hact : ∀ w : X, w ∈ centralizer (Z : Set X) → Odd (orderOf w) → ∃ j ∈ U, φ w = φ j := by
    intro w hwZ hwo
    obtain ⟨j, hj, hjw⟩ := exists_mem_conj_eq_of_odd_of_aSeven e
      (by rw [normalizer_eq_top]; exact mem_top w) hwo
    have hc : j⁻¹ * w ∈ centralizer (L : Set X) := by
      rw [mem_centralizer_iff]
      intro m hm
      have h := hjw m hm
      calc m * (j⁻¹ * w) = j⁻¹ * (j * m * j⁻¹) * w := by group
        _ = j⁻¹ * (w * m * w⁻¹) * w := by rw [h]
        _ = j⁻¹ * w * m := by group
    have hjo : Odd (orderOf j) := by
      have hd := orderOf_dvd_orderOf_mul_of_mem_centralizer hLC hj hc
      rw [mul_inv_cancel_left] at hd
      exact hwo.of_dvd_nat hd
    have hjz : j ∈ centralizer ({z} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      have h2 : w * z * w⁻¹ = z := by
        rw [← mem_centralizer_iff.mp hwZ z hz]
        group
      have h3 : j * z * j⁻¹ = z := (hjw z (hZL hz)).symm.trans h2
      calc j * z = j * z * j⁻¹ * j := by group
        _ = z * j := by rw [h3]
    refine ⟨j, hodd j ⟨hj, hjz⟩ hjo, MulEquiv.ext fun m => Subtype.ext ?_⟩
    simp only [φ, MulAut.conjNormal_apply]
    exact hjw m m.2
  obtain ⟨jx, hjx, hx⟩ := hact x hxZ hxo
  obtain ⟨jy, hjy, hy⟩ := hact y hyZ hyo
  have hjxy : ⁅jx, jy⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm_of_isCyclic hUcyc hjx hjy)
  have h1 : φ ⁅x, y⁆ = 1 := by
    rw [map_commutatorElement, hx, hy, ← map_commutatorElement, hjxy, map_one]
  rw [mem_centralizer_iff]
  intro m hm
  have h2 := congrArg (fun f : MulAut L => ((f ⟨m, hm⟩ : L) : X)) h1
  simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at h2
  calc m * ⁅x, y⁆ = ⁅x, y⁆ * m * ⁅x, y⁆⁻¹ * ⁅x, y⁆ := by rw [h2]
    _ = ⁅x, y⁆ * m := by group

theorem commutatorElement_mem_centralizer_of_le {L D Z : Subgroup X} (hL : L.Normal)
    (hD : D.Normal) (hDL : D ≤ L) {qmin : ℕ} (hDs : IsL2OrA7 D qmin)
    (hLD : L ⊓ centralizer (D : Set X) = ⊥) (hZL : Z ≤ L)
    (hCZ : ∀ l ∈ L, l ∈ centralizer (Z : Set X) → Odd (orderOf l) → l = 1) {x y : X}
    (hxy : ⁅x, y⁆ ∈ centralizer (Z : Set X)) (hxyo : Odd (orderOf ⁅x, y⁆)) :
    ⁅x, y⁆ ∈ centralizer (L : Set X) := by
  have := hD
  have hmem : ⁅x, y⁆ ∈ D ⊔ centralizer (D : Set X) :=
    commutator_le_sup_centralizer_of_isL2OrA7 D hDs
      (Subgroup.commutator_mem_commutator (mem_top x) (mem_top y))
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hmem
  obtain ⟨d, hd, c, hc, hdc⟩ := hmem
  have hdc' : d * c = ⁅x, y⁆ := hdc
  have hcD : ∀ m ∈ D, m * c = c * m := mem_centralizer_iff.mp hc
  have hcL : c ∈ centralizer (L : Set X) := by
    rw [mem_centralizer_iff]
    intro g hg
    have hdL : g⁻¹ * (c * g * c⁻¹) ∈ L := L.mul_mem (L.inv_mem hg) (hL.conj_mem g hg c)
    have hdD : g⁻¹ * (c * g * c⁻¹) ∈ centralizer (D : Set X) := by
      rw [mem_centralizer_iff]
      intro m hm
      have h2 := hcD _ (hD.conj_mem m hm g)
      have h3 : c⁻¹ * m = m * c⁻¹ := (Commute.inv_left (hcD m hm).symm).eq
      calc m * (g⁻¹ * (c * g * c⁻¹)) = g⁻¹ * ((g * m * g⁻¹) * c) * g * c⁻¹ := by group
        _ = g⁻¹ * (c * (g * m * g⁻¹)) * g * c⁻¹ := by rw [h2]
        _ = g⁻¹ * c * g * (m * c⁻¹) := by group
        _ = g⁻¹ * c * g * (c⁻¹ * m) := by rw [← h3]
        _ = g⁻¹ * (c * g * c⁻¹) * m := by group
    have h4 : g⁻¹ * (c * g * c⁻¹) ∈ L ⊓ centralizer (D : Set X) := ⟨hdL, hdD⟩
    rw [hLD, mem_bot] at h4
    have h5 : c * g * c⁻¹ = g := (inv_mul_eq_one.mp h4).symm
    calc g * c = c * g * c⁻¹ * c := by rw [h5]
      _ = c * g := by group
  have hcZ : c ∈ centralizer (Z : Set X) := Subgroup.centralizer_le hZL hcL
  have hdZ : d ∈ centralizer (Z : Set X) := by
    rw [eq_mul_inv_of_mul_eq hdc']
    exact (centralizer _).mul_mem hxy ((centralizer _).inv_mem hcZ)
  have hdo : Odd (orderOf d) := by
    have h := orderOf_dvd_orderOf_mul_of_mem_centralizer
      (inf_centralizer_eq_bot_of_isL2OrA7 D hDs) hd hc
    rw [hdc'] at h
    exact hxyo.of_dvd_nat h
  have hd1 : d = 1 := hCZ d (hDL hd) hdZ hdo
  rw [← hdc', hd1, one_mul]
  exact hcL

theorem commutatorElement_mem_centralizer_of_isL2OrA7
    [Finite X] {L Z : Subgroup X} (hL : L.Normal)
    (hLs : IsL2OrA7 L 5) (hZ : IsKleinFour Z) (hZL : Z ≤ L) {x y : X}
    (hxZ : x ∈ centralizer (Z : Set X)) (hyZ : y ∈ centralizer (Z : Set X))
    (hxo : Odd (orderOf x)) (hyo : Odd (orderOf y)) (hxyo : Odd (orderOf ⁅x, y⁆)) :
    ⁅x, y⁆ ∈ centralizer (L : Set X) := by
  rcases hLs with ⟨⟨e⟩⟩ | ⟨r, k, hr, hr2, hq, ⟨e⟩⟩
  · exact commutatorElement_mem_centralizer_of_aSeven hL e hZ hZL hxZ hyZ hxo hyo
  · have := hr
    have hLs : IsL2OrA7 L 5 := Or.inr ⟨r, k, hr, hr2, hq, ⟨e⟩⟩
    have hxy : ⁅x, y⁆ ∈ centralizer (Z : Set X) := by
      rw [commutatorElement_def]
      exact (centralizer _).mul_mem ((centralizer _).mul_mem ((centralizer _).mul_mem hxZ hyZ)
        ((centralizer _).inv_mem hxZ)) ((centralizer _).inv_mem hyZ)
    refine commutatorElement_mem_centralizer_of_le hL hL le_rfl hLs
      (inf_centralizer_eq_bot_of_isL2OrA7 L hLs) hZL ?_ hxy hxyo
    intro l hl hlZ hlo
    have h := inf_eq_bot_of_odd_of_le_centralizer_kleinFour hr2 hq e hZ hZL (U := zpowers l)
      (by rw [Nat.card_zpowers]; exact hlo) (zpowers_le.mpr hlZ)
    have hl' : l ∈ zpowers l ⊓ L := ⟨mem_zpowers l, hl⟩
    rw [h, mem_bot] at hl'
    exact hl'

theorem pgl2_commutator_eq_range_toPGL {F : Type} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) :
    commutator (PGL2 F) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  by_cases h3 : Nat.card F = 3
  · have hle := CFSG.GorensteinWalter.pgl2_commutator_le_psl2_range F
    have : Fintype F := Fintype.ofFinite F
    let eK : ZMod 3 ≃+* F :=
      ZMod.ringEquivOfPrime F Nat.prime_three (by simpa [Nat.card_eq_fintype_card] using h3)
    let e₄ : PGL2 F ≃* Equiv.Perm (Fin 4) :=
      (CFSG.GorensteinWalter.pgl2RingEquiv eK).symm.trans
        CFSG.GorensteinWalter.pgl2_three_equiv_perm
    obtain ⟨eA⟩ :=
      CFSG.GorensteinWalter.commutator_mulEquiv_alternatingGroup_of_mulEquiv_perm_four e₄
    have hcA : Nat.card (commutator (PGL2 F)) = 12 := by
      rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card]
      have h := two_mul_card_alternatingGroup (α := Fin 4)
      rw [Fintype.card_perm, Fintype.card_fin] at h
      have h24 : Nat.factorial 4 = 24 := rfl
      omega
    have hcP : Nat.card (PGL2 F) = 24 := by
      rw [Nat.card_congr e₄.toEquiv, Nat.card_perm, Nat.card_fin]
      rfl
    have hcJ : Nat.card
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range = 12 := by
      have h := Subgroup.card_mul_index
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range
      rw [pgl2_index_range_toPGL hF, hcP] at h
      omega
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcA, hcJ])
  · exact CFSG.GorensteinWalter.pgl2_commutator_eq_psl2_range_of_card_gt_three F hF
      (lt_of_le_of_ne (three_le_of_isOddPrimePower hF) (Ne.symm h3))

theorem commutatorElement_mem_centralizer_of_pgl2
    [Finite X] {L Z : Subgroup X} (hL : L.Normal) {p k : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hq : 3 ≤ p ^ k) (e : L ≃* PGL2 (GaloisField p k))
    (hZ : IsKleinFour Z) (hZL : Z ≤ L) {x y : X} (hxy : ⁅x, y⁆ ∈ centralizer (Z : Set X))
    (hxyo : Odd (orderOf ⁅x, y⁆)) : ⁅x, y⁆ ∈ centralizer (L : Set X) := by
  have hF : IsOddPrimePower (Nat.card (GaloisField p k)) := isOddPrimePower_card_galoisField hp2 hq
  set f : PGL2 (GaloisField p k) →* X := L.subtype.comp e.symm.toMonoidHom with hfdef
  have hf : Function.Injective f := L.subtype_injective.comp e.symm.injective
  have hfr : f.range = L := range_subtype_comp_symm e
  set ι := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := GaloisField p k) with hι
  set D : Subgroup X := ι.range.map f with hDdef
  have hDeq : D = ⁅L, L⁆ := by
    rw [hDdef, ← pgl2_commutator_eq_range_toPGL hF, map_commutator_eq, hfr]
  have := hL
  have hDn : D.Normal := by rw [hDeq]; infer_instance
  have hDL : D ≤ L := by rw [hDeq]; exact Subgroup.commutator_le_left L L
  have hDs : IsL2OrA7 D 3 := by
    refine Or.inr ⟨p, k, inferInstance, hp2, hq, ⟨?_⟩⟩
    have hDr : D = (f.comp ι).range := by rw [hDdef, MonoidHom.range_comp]
    have hinj : Function.Injective (f.comp ι) := fun a b h =>
      Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (hf h)
    exact (MulEquiv.subgroupCongr hDr).trans (MonoidHom.ofInjective hinj).symm
  have hLD : L ⊓ centralizer (D : Set X) = ⊥ := by
    rw [eq_bot_iff]
    rintro x' ⟨hx'L, hx'D⟩
    rw [← hfr] at hx'L
    obtain ⟨y', rfl⟩ := hx'L
    have hy' : y' ∈ centralizer (ι.range : Set (PGL2 (GaloisField p k))) := by
      rw [mem_centralizer_iff]
      intro j hj
      apply hf
      rw [map_mul, map_mul]
      exact mem_centralizer_iff.mp hx'D (f j) ⟨j, hj, rfl⟩
    rw [CFSG.GorensteinWalter.pgl2_psl2Range_centralizer_eq_bot _ hF, mem_bot] at hy'
    rw [hy', map_one]
    exact one_mem _
  have hCZ : ∀ l ∈ L, l ∈ centralizer (Z : Set X) → Odd (orderOf l) → l = 1 := by
    intro l hl hlZ hlo
    have hZr : Z ≤ f.range := hfr ▸ hZL
    have hZ' := isKleinFour_comap f hf hZ hZr
    rw [← hfr] at hl
    obtain ⟨y', rfl⟩ := hl
    have hy' : y' ∈ centralizer ((Z.comap f : Subgroup _) : Set (PGL2 (GaloisField p k))) := by
      rw [mem_centralizer_iff]
      intro z hz
      apply hf
      rw [map_mul, map_mul]
      exact mem_centralizer_iff.mp hlZ (f z) hz
    rw [pgl2_centralizer_kleinFour hF hZ'] at hy'
    have h := eq_bot_of_le_of_isKleinFour hZ (zpowers_le.mpr hy') (by rwa [Nat.card_zpowers])
    exact zpowers_eq_bot.mp h
  exact commutatorElement_mem_centralizer_of_le hL hDn hDL hDs hLD hZL hCZ hxy hxyo

end Commutation


theorem isMaxInvIn_of_forall_le
    {X : Type*} [Group X] [Finite X] {L V : Subgroup X} (hL : IsL2OrA7 L 5) (hV : IsKleinFour V)
    (hVL : V ≤ L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {v : X} (hv : v ∈ V) (hv1 : v ≠ 1)
    {R : Subgroup X} (hRC : R ≤ L ⊓ centralizer ({v} : Set X)) (hR : IsPGroup p R)
    (hall : ∀ R' : Subgroup X, R' ≤ L ⊓ centralizer ({v} : Set X) → IsPGroup p R' → R' ≤ R) :
    IsMaxInvIn p V L R := by
  have hVv : V ≤ centralizer ({v} : Set X) := fun u hu =>
    mem_centralizer_singleton_iff.mpr (mul_comm_of_mem_kleinFour hV hu hv)
  have hVN : V ≤ normalizer ((L ⊓ centralizer ({v} : Set X) : Subgroup X) : Set X) :=
    fun u hu => normalizer_inf_centralizer_le_normalizer_inf ⟨le_normalizer (hVL hu), hVv hu⟩
  refine ⟨hRC.trans inf_le_left, hR, hVN.trans (normalizer_le_normalizer_of_forall_le hRC hR hall),
    fun W hWL hW hVW hRW => ?_⟩
  obtain ⟨v', hv', hv'1, hWv'⟩ := exists_le_centralizer_of_odd_of_kleinFour_le_normalizer
    (Or.inl hL) hV hVL hWL (odd_card_of_isPGroup hp hp2 hW) hVW
  have hv'2 : orderOf v' = 2 := orderOf_eq_prime (sq_eq_one_of_mem_kleinFour hV hv') hv'1
  obtain ⟨R', hR', hR'all⟩ :=
    exists_isSylowOf_inf_centralizer_forall_le (Or.inl hL) hp hp2 (hVL hv') hv'2
  have hWR' : W ≤ R' := hR'all W (le_inf hWL hWv') hW
  obtain ⟨g, ⟨hgL, -⟩, hg⟩ := exists_conj_eq_of_mem_kleinFour hL hV hVL hv hv1 hv' hv'1
  have h1 : R.map (MulAut.conj g).toMonoidHom ≤ R' := by
    apply hR'all _ _ (hR.map _)
    rintro _ ⟨r, hr, rfl⟩
    have hr' := hRC hr
    refine Subgroup.mem_inf.mpr ⟨L.mul_mem (L.mul_mem hgL hr'.1) (L.inv_mem hgL), ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hrv : r * v = v * r := mem_centralizer_singleton_iff.mp hr'.2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hg]
    calc g * r * g⁻¹ * (g * v * g⁻¹) = g * (r * v) * g⁻¹ := by group
      _ = g * (v * r) * g⁻¹ := by rw [hrv]
      _ = g * v * g⁻¹ * (g * r * g⁻¹) := by group
  have h2 : R'.map (MulAut.conj g⁻¹).toMonoidHom ≤ R := by
    apply hall _ _ (hR'.isPGroup.map _)
    rintro _ ⟨r, hr, rfl⟩
    have hr' := hR'.le hr
    refine Subgroup.mem_inf.mpr
      ⟨L.mul_mem (L.mul_mem (L.inv_mem hgL) hr'.1) (L.inv_mem (L.inv_mem hgL)), ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hrv : r * v' = v' * r := mem_centralizer_singleton_iff.mp hr'.2
    have hv_eq : v = g⁻¹ * v' * g := by rw [← hg]; group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hv_eq]
    calc g⁻¹ * r * g * (g⁻¹ * v' * g) = g⁻¹ * (r * v') * g := by group
      _ = g⁻¹ * (v' * r) * g := by rw [hrv]
      _ = g⁻¹ * v' * g * (g⁻¹ * r * g) := by group
  have hc2 : Nat.card R' ≤ Nat.card R := by
    have hinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
    have h := Subgroup.card_le_of_le h2
    rwa [card_map_of_injective hinj] at h
  have hRR' : R = R' := Subgroup.eq_of_le_of_card_ge (hRW.trans hWR') hc2
  exact le_antisymm (hWR'.trans hRR'.ge) hRW

theorem exists_isSylowOf_centralizer_forall_le
    {Γ : Type*} [Group Γ] [Finite Γ] (hO : CFSG.oddCore Γ = ⊥)
    {L L₁ Z V : Subgroup Γ} (hL : L.Normal) (hL₁ : L₁.Normal) (hLs : IsL2OrA7 L 5)
    (hL₁s : IsL2PGL2OrA7OrV4 L₁ ∨ IsPGroup 2 L₁) (hL₁L : L₁ ≤ centralizer (L : Set Γ))
    (hV : IsKleinFour V) (hVL : V ≤ L) (hZ : IsKleinFour Z) (hZL₁ : Z ≤ L₁)
    (hsyl : IsSylowOf 2 (Z ⊔ V) (centralizer ((Z ⊔ V : Subgroup Γ) : Set Γ))) {t : ℕ}
    (ht : t.Prime) (ht2 : t ≠ 2) :
    ∃ Q₀ : Subgroup Γ, IsSylowOf t Q₀ (centralizer ((Z ⊔ V : Subgroup Γ) : Set Γ)) ∧
      ∀ R : Subgroup Γ, R ≤ centralizer ((Z ⊔ V : Subgroup Γ) : Set Γ) → IsPGroup t R →
        R ≤ Q₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hL
  have := hL₁
  set A := Z ⊔ V with hAdef
  set H₀ := centralizer (A : Set Γ) with hH₀def
  obtain ⟨hAH₀, hA2, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hsyl
  have hcent : ∀ x ∈ H₀, ∀ q ∈ A, x * q = q * x := fun x hx q hq =>
    (mem_centralizer_iff.mp hx q hq).symm
  obtain ⟨K, hKH₀, hKiff, -, hdec⟩ :=
    CFSG.GroupTheory.exists_complement_of_central_sylow hAH₀ hA2 hcent hidx
  have hKodd : ∀ x ∈ K, Odd (orderOf x) := fun x hx =>
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp ((hKiff x (hKH₀ hx)).mp hx))
  have hKall : ∀ x ∈ H₀, Odd (orderOf x) → x ∈ K := fun x hx hxo =>
    (hKiff x hx).mpr fun h => (Nat.not_even_iff_odd.mpr hxo) (even_iff_two_dvd.mpr h)
  have hodd_card : ∀ N : Subgroup Γ, N ≤ K → Odd (Nat.card N) := by
    intro N hNK
    by_contra h
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at h
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h
    have h' := hKodd g (hNK g.2)
    rw [Subgroup.orderOf_coe, hg] at h'
    exact absurd h' (by decide)
  have hZH : H₀ ≤ centralizer (Z : Set Γ) := Subgroup.centralizer_le (le_sup_left : Z ≤ A)
  have hVH : H₀ ≤ centralizer (V : Set Γ) := Subgroup.centralizer_le (le_sup_right : V ≤ A)
  have hCLL₁ : centralizer (L : Set Γ) ⊓ centralizer (L₁ : Set Γ) ≤ H₀ := fun x hx =>
    mem_centralizer_sup_of_mem (Subgroup.centralizer_le hZL₁ hx.2)
      (Subgroup.centralizer_le hVL hx.1)
  have hN : centralizer (L : Set Γ) ⊓ centralizer (L₁ : Set Γ) ⊓ K = ⊥ := by
    have hn : (centralizer (L : Set Γ) ⊓ centralizer (L₁ : Set Γ) ⊓ K).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have h1 : g * n * g⁻¹ ∈ centralizer (L : Set Γ) ⊓ centralizer (L₁ : Set Γ) :=
        ⟨(inferInstance : (centralizer (L : Set Γ)).Normal).conj_mem n hn.1.1 g,
          (inferInstance : (centralizer (L₁ : Set Γ)).Normal).conj_mem n hn.1.2 g⟩
      refine ⟨h1, hKall _ (hCLL₁ h1) ?_⟩
      have h2 : orderOf (g * n * g⁻¹) = orderOf n :=
        orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective n
      rw [h2]
      exact hKodd n hn.2
    have h := le_oddCore_of_normal_of_odd hn (hodd_card _ inf_le_right)
    rw [hO] at h
    exact le_bot_iff.mp h
  have hcommK : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ K := fun x hx y hy => by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx)) (K.inv_mem hy)
  have hLcomm : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ centralizer (L : Set Γ) := fun x hx y hy =>
    commutatorElement_mem_centralizer_of_isL2OrA7 hL hLs hV hVL (hVH (hKH₀ hx)) (hVH (hKH₀ hy))
      (hKodd x hx) (hKodd y hy) (hKodd _ (hcommK x hx y hy))
  have hL₁two : IsPGroup 2 L₁ → L₁ ≤ centralizer (K : Set Γ) := by
    intro h2
    have hZ2 : IsPGroup 2 Z := IsPGroup.of_card (n := 2) (by rw [hZ.card_four]; norm_num)
    refine le_centralizer_of_thompson_AxB h2 (Nat.coprime_two_right.mpr (hodd_card K le_rfl))
      hZ2 le_normalizer_of_normal le_normalizer_of_normal
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hKH₀.trans hZH)) ?_
    rintro x ⟨hxL₁, hxZ⟩
    have hxH : x ∈ H₀ :=
      mem_centralizer_sup_of_mem hxZ (Subgroup.centralizer_le hVL (hL₁L hxL₁))
    obtain ⟨n, hn⟩ := h2 ⟨x, hxL₁⟩
    have hn' : x ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
    obtain ⟨q, hq, o, ho, rfl⟩ := hdec x hxH
    obtain ⟨m, hm⟩ := hA2 ⟨q, hq⟩
    have hm' : q ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
    have hqo : Commute q o := mem_centralizer_iff.mp (hKH₀ ho) q hq
    have ho1 : o ^ 2 ^ (n + m) = 1 := by
      have h1 : q ^ 2 ^ n * o ^ 2 ^ n = 1 := by rw [← hqo.mul_pow, hn']
      have h2 : o ^ 2 ^ n = (q ^ 2 ^ n)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [pow_add, pow_mul, h2, inv_pow, ← pow_mul, mul_comm, pow_mul, hm', one_pow, inv_one]
    have hord : orderOf o = 1 := Nat.Coprime.eq_one_of_dvd
      ((Nat.coprime_two_right.mpr (hKodd o ho)).pow_right (n + m)) (orderOf_dvd_of_pow_eq_one ho1)
    rw [orderOf_eq_one_iff.mp hord, mul_one]
    exact le_centralizer_iff.mp hKH₀ hq
  have hL₁comm : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ centralizer (L₁ : Set Γ) := by
    intro x hx y hy
    have hxy_two : IsPGroup 2 L₁ → ⁅x, y⁆ ∈ centralizer (L₁ : Set Γ) := fun h2 => by
      have hK : K ≤ centralizer (L₁ : Set Γ) := le_centralizer_iff.mp (hL₁two h2)
      rw [commutatorElement_def]
      exact (centralizer _).mul_mem ((centralizer _).mul_mem ((centralizer _).mul_mem (hK hx)
        (hK hy)) ((centralizer _).inv_mem (hK hx))) ((centralizer _).inv_mem (hK hy))
    rcases hL₁s with (h | ⟨p', k', hp', hp'2, hq', ⟨e₁⟩⟩ | h4) | h2
    · exact commutatorElement_mem_centralizer_of_isL2OrA7 hL₁ h hZ hZL₁ (hZH (hKH₀ hx))
        (hZH (hKH₀ hy)) (hKodd x hx) (hKodd y hy) (hKodd _ (hcommK x hx y hy))
    · have := hp'
      exact commutatorElement_mem_centralizer_of_pgl2 hL₁ hp'2 hq' e₁ hZ hZL₁
        (hZH (hKH₀ (hcommK x hx y hy))) (hKodd _ (hcommK x hx y hy))
    · exact hxy_two (IsPGroup.of_card (n := 2) (by rw [h4.card_four]; norm_num))
    · exact hxy_two h2
  have hKcomm : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
    intro x hx y hy
    have h : ⁅x, y⁆ ∈ centralizer (L : Set Γ) ⊓ centralizer (L₁ : Set Γ) ⊓ K :=
      ⟨⟨hLcomm x hx y hy, hL₁comm x hx y hy⟩, hcommK x hx y hy⟩
    rw [hN, mem_bot] at h
    exact commutatorElement_eq_one_iff_mul_comm.mp h
  exact exists_isSylowOf_forall_le_of_odd_mem hKH₀ hKcomm hKall ht ht2


theorem exists_isMaxInvIn_mul_comm_of_permutable
    {Γ : Type} [Group Γ] [Finite Γ] (hO : CFSG.oddCore Γ = ⊥) {L L₁ Z V : Subgroup Γ}
    (hL : L.Normal) (hL₁ : L₁.Normal) (hLs : IsL2OrA7 L 5)
    (hL₁s : IsL2PGL2OrA7OrV4 L₁ ∨ IsPGroup 2 L₁) (hL₁L : L₁ ≤ centralizer (L : Set Γ))
    (_hinf : L ⊓ L₁ = ⊥) (hV : IsKleinFour V) (hVL : V ≤ L) (hZ : IsKleinFour Z)
    (hZL₁ : Z ≤ L₁) (_hΓ : L₁ ⊔ L ⊔ normalizer ((Z ⊔ V : Subgroup Γ) : Set Γ) = ⊤)
    (hsyl : IsSylowOf 2 (Z ⊔ V) (centralizer ((Z ⊔ V : Subgroup Γ) : Set Γ)))
    {p t : ℕ} (hp : p.Prime) (ht : t.Prime) (hp2 : p ≠ 2) (ht2 : t ≠ 2) (hpt : p ≠ t)
    {P F : Subgroup Γ} (hP : IsMaxInvIn p (Z ⊔ V) ⊤ P) (hZP : Z ≤ centralizer (P : Set Γ))
    (hF : IsPGroup t F) (hAF : Z ⊔ V ≤ normalizer (F : Set Γ))
    (hFP : (F : Set Γ) * (P : Set Γ) = (P : Set Γ) * (F : Set Γ)) :
    ∃ F' : Subgroup Γ, IsMaxInvIn t (Z ⊔ V) ⊤ F' ∧ F ≤ F' ∧
      (F' : Set Γ) * (P : Set Γ) = (P : Set Γ) * (F' : Set Γ) := by
  have := hL
  have := hL₁
  set A := Z ⊔ V with hAdef
  set H₀ := centralizer (A : Set Γ) with hH₀def
  have hA2 : IsPGroup 2 A := hsyl.isPGroup
  have hAH₀ : A ≤ H₀ := hsyl.le
  have hZC : Z ≤ centralizer (L : Set Γ) := hZL₁.trans hL₁L
  have hZCV : Z ≤ centralizer (V : Set Γ) := fun z hz => Subgroup.centralizer_le hVL (hZC hz)
  have hZV : Z ≤ normalizer (V : Set Γ) := fun z hz => centralizer_le_normalizer _ (hZCV hz)
  have hZH : H₀ ≤ centralizer (Z : Set Γ) := Subgroup.centralizer_le (le_sup_left : Z ≤ A)
  have hdecomp : ∀ {r : ℕ} (W : Subgroup Γ), r.Prime → r ≠ 2 → IsPGroup r W →
      A ≤ normalizer (W : Set Γ) → W ≤ W ⊓ L₁ ⊔ W ⊓ L ⊔ W ⊓ H₀ := fun W hr hr2 hW hAW =>
    (le_commutator_sup_inf_centralizer_of_isPGroup hr hr2 hA2 hW hAW).trans
      (sup_le_sup_right (commutator_sup_le_sup_inf hL hL₁ hVL hZL₁ hZV hAW) _)
  obtain ⟨Q₀, hQ₀, hQ₀all⟩ := exists_isSylowOf_centralizer_forall_le hO hL hL₁ hLs hL₁s hL₁L hV
    hVL hZ hZL₁ hsyl ht ht2
  have hH₀Q₀ : H₀ ≤ normalizer (Q₀ : Set Γ) :=
    le_normalizer.trans (normalizer_le_normalizer_of_forall_le hQ₀.le hQ₀.isPGroup hQ₀all)
  have hPp : IsPGroup p P := hP.2.1
  have hcop : Nat.Coprime (Nat.card F) (Nat.card P) := by
    have : Fact t.Prime := ⟨ht⟩
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨a, ha⟩ := hF.exists_card_eq
    obtain ⟨b, hb⟩ := hPp.exists_card_eq
    rw [ha, hb]
    exact Nat.Coprime.pow a b ((Nat.coprime_primes ht hp).mpr (Ne.symm hpt))
  have hFPodd := odd_card_sup_of_mul_comm hFP hcop (odd_card_of_isPGroup ht ht2 hF)
    (odd_card_of_isPGroup hp hp2 hPp)
  obtain ⟨v, hv, hv1, hFPv⟩ := exists_le_centralizer_of_odd_of_le_normalizer hLs hV hVL
    le_normalizer_of_normal hFPodd
    (le_normalizer_sup_of_le_normalizer ((le_sup_right : V ≤ A).trans hAF)
      ((le_sup_right : V ≤ A).trans hP.2.2.1))
  have hv2 : orderOf v = 2 := orderOf_eq_prime (sq_eq_one_of_mem_kleinFour hV hv) hv1
  have hFv : F ≤ centralizer ({v} : Set Γ) := le_sup_left.trans hFPv
  have hPv : P ≤ centralizer ({v} : Set Γ) := le_sup_right.trans hFPv
  obtain ⟨Rt, hRt, hRtall⟩ :=
    exists_isSylowOf_inf_centralizer_forall_le (Or.inl hLs) ht ht2 (hVL hv) hv2
  obtain ⟨Rp, hRp, hRpall⟩ :=
    exists_isSylowOf_inf_centralizer_forall_le (Or.inl hLs) hp hp2 (hVL hv) hv2
  have hRtmax : IsMaxInvIn t V L Rt :=
    isMaxInvIn_of_forall_le hLs hV hVL ht ht2 hv hv1 hRt.le hRt.isPGroup hRtall
  have hNRt : normalizer (L : Set Γ) ⊓ centralizer ({v} : Set Γ) ≤ normalizer (Rt : Set Γ) :=
    normalizer_inf_centralizer_le_normalizer_inf.trans
      (normalizer_le_normalizer_of_forall_le hRt.le hRt.isPGroup hRtall)
  have hNRp : normalizer (L : Set Γ) ⊓ centralizer ({v} : Set Γ) ≤ normalizer (Rp : Set Γ) :=
    normalizer_inf_centralizer_le_normalizer_inf.trans
      (normalizer_le_normalizer_of_forall_le hRp.le hRp.isPGroup hRpall)
  have hNv : ∀ {W : Subgroup Γ}, W ≤ centralizer ({v} : Set Γ) →
      W ≤ normalizer (L : Set Γ) ⊓ centralizer ({v} : Set Γ) := fun hW =>
    le_inf le_normalizer_of_normal hW
  have hH₀v : H₀ ≤ centralizer ({v} : Set Γ) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hx v (mem_sup_right hv)).symm
  have hAv : A ≤ centralizer ({v} : Set Γ) := sup_le
    (fun z hz =>
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hZC hz) v (hVL hv)).symm)
    (fun u hu => mem_centralizer_singleton_iff.mpr (mul_comm_of_mem_kleinFour hV hu hv))
  obtain ⟨Q₁, hQ₁max, hFQ₁⟩ := exists_isMaxInvIn_le (A := Z) (H := L₁) (Q := F ⊓ L₁)
    inf_le_right (hF.to_le inf_le_left)
    (le_normalizer_inf_of_le_normalizer ((le_sup_left : Z ≤ A).trans hAF) le_normalizer_of_normal)
  have hQ₁N : normalizer (L₁ : Set Γ) ⊓ centralizer (Z : Set Γ) ≤ normalizer (Q₁ : Set Γ) := by
    rcases hL₁s with h | h2
    · exact normalizer_inf_centralizer_le_normalizer_of_isMaxInvIn h hZ hZL₁ ht ht2 hQ₁max
    · have hQ₁bot : Q₁ = ⊥ := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have : Fact t.Prime := ⟨ht⟩
        obtain ⟨a, ha⟩ := (h2.to_le hQ₁max.1).exists_card_eq
        obtain ⟨b, hb⟩ := hQ₁max.2.1.exists_card_eq
        have hc : Nat.Coprime (2 ^ a) (t ^ b) :=
          Nat.Coprime.pow a b ((Nat.coprime_primes Nat.prime_two ht).mpr (Ne.symm ht2))
        rw [← ha, ← hb] at hc
        exact Subgroup.card_eq_one.mp ((Nat.coprime_self _).mp hc)
      intro x _
      rw [hQ₁bot]
      exact le_normalizer_of_normal (K := ⊤) (mem_top x)
  have hPZ : P ≤ centralizer (Z : Set Γ) := le_centralizer_iff.mp hZP
  have hACZ : A ≤ centralizer (Z : Set Γ) := sup_le
    (fun z hz => mem_centralizer_iff.mpr fun h hh => mul_comm_of_mem_kleinFour hZ hh hz)
    (le_centralizer_iff.mp hZCV)
  have hPQ₁ : P ≤ normalizer (Q₁ : Set Γ) := fun x hx =>
    hQ₁N ⟨le_normalizer_of_normal hx, hPZ hx⟩
  have hQ₀Q₁ : Q₀ ≤ normalizer (Q₁ : Set Γ) := fun x hx =>
    hQ₁N ⟨le_normalizer_of_normal hx, hZH (hQ₀.le hx)⟩
  have hAQ₁ : A ≤ normalizer (Q₁ : Set Γ) := fun a ha =>
    hQ₁N ⟨le_normalizer_of_normal ha, hACZ ha⟩
  have hQ₀Rt : Q₀ ≤ normalizer (Rt : Set Γ) := (hNv (hQ₀.le.trans hH₀v)).trans hNRt
  have hQ₀Rp : Q₀ ≤ normalizer (Rp : Set Γ) := (hNv (hQ₀.le.trans hH₀v)).trans hNRp
  have hPRt : P ≤ normalizer (Rt : Set Γ) := (hNv hPv).trans hNRt
  have hPRp : P ≤ normalizer (Rp : Set Γ) := (hNv hPv).trans hNRp
  have hARt : A ≤ normalizer (Rt : Set Γ) := (hNv hAv).trans hNRt
  have hARp : A ≤ normalizer (Rp : Set Γ) := (hNv hAv).trans hNRp
  have hAQ₀ : A ≤ normalizer (Q₀ : Set Γ) := hAH₀.trans hH₀Q₀
  set Nt := Q₁ ⊔ Rt with hNtdef
  set F' := Nt ⊔ Q₀ with hF'def
  have hQ₁Rt : Q₁ ≤ normalizer (Rt : Set Γ) := fun x hx =>
    centralizer_le_normalizer _
      (Subgroup.centralizer_le (hRt.le.trans inf_le_left) (hL₁L (hQ₁max.1 hx)))
  have hNtt : IsPGroup t Nt := IsPGroup.to_sup_of_normal_right' hQ₁max.2.1 hRt.isPGroup hQ₁Rt
  have hQ₀Nt : Q₀ ≤ normalizer (Nt : Set Γ) := le_normalizer_sup_of_le_normalizer hQ₀Q₁ hQ₀Rt
  have hF't : IsPGroup t F' := IsPGroup.to_sup_of_normal_left' hNtt hQ₀.isPGroup hQ₀Nt
  have hAF' : A ≤ normalizer (F' : Set Γ) :=
    le_normalizer_sup_of_le_normalizer (le_normalizer_sup_of_le_normalizer hAQ₁ hARt) hAQ₀
  have hFF' : F ≤ F' := by
    refine (hdecomp F ht ht2 hF hAF).trans (sup_le (sup_le ?_ ?_) ?_)
    · exact hFQ₁.trans (le_sup_left.trans le_sup_left)
    · exact (hRtall (F ⊓ L) (le_inf inf_le_right (inf_le_left.trans hFv))
        (hF.to_le inf_le_left)).trans (le_sup_right.trans le_sup_left)
    · exact (hQ₀all (F ⊓ H₀) inf_le_right (hF.to_le inf_le_left)).trans le_sup_right
  have hmax : ∀ Q : Subgroup Γ, Q ≤ ⊤ → IsPGroup t Q → A ≤ normalizer (Q : Set Γ) →
      F' ≤ Q → Q = F' := by
    intro Q _ hQt hAQ hF'Q
    refine le_antisymm ((hdecomp Q ht ht2 hQt hAQ).trans (sup_le (sup_le ?_ ?_) ?_)) hF'Q
    · have h := hQ₁max.2.2.2 (Q ⊓ L₁) inf_le_right (hQt.to_le inf_le_left)
        (le_normalizer_inf_of_le_normalizer ((le_sup_left : Z ≤ A).trans hAQ)
          le_normalizer_of_normal)
        (le_inf ((le_sup_left.trans le_sup_left).trans hF'Q) hQ₁max.1)
      rw [h]
      exact le_sup_left.trans le_sup_left
    · have h := hRtmax.2.2.2 (Q ⊓ L) inf_le_right (hQt.to_le inf_le_left)
        (le_normalizer_inf_of_le_normalizer ((le_sup_right : V ≤ A).trans hAQ)
          le_normalizer_of_normal)
        (le_inf ((le_sup_right.trans le_sup_left).trans hF'Q) (hRt.le.trans inf_le_left))
      rw [h]
      exact le_sup_right.trans le_sup_left
    · exact (hQ₀all (Q ⊓ H₀) inf_le_right (hQt.to_le inf_le_left)).trans le_sup_right
  have hPdec := hdecomp P hp hp2 hPp hP.2.2.1
  have hPL₁ : P ⊓ L₁ ≤ P ⊓ H₀ := fun x hx =>
    ⟨hx.1, mem_centralizer_sup_of_mem (hPZ hx.1) (Subgroup.centralizer_le hVL (hL₁L hx.2))⟩
  have hPL : P ⊓ L ≤ Rp :=
    hRpall (P ⊓ L) (le_inf inf_le_right (inf_le_left.trans hPv)) (hPp.to_le inf_le_left)
  have hRpP : Rp ≤ P := by
    have h := hP.2.2.2 (P ⊔ Rp) le_top (IsPGroup.to_sup_of_normal_right' hPp hRp.isPGroup hPRp)
      (le_normalizer_sup_of_le_normalizer hP.2.2.1 hARp) le_sup_left
    exact le_sup_right.trans h.le
  set Cp := P ⊓ H₀ with hCpdef
  have hPeq : P = Rp ⊔ Cp := le_antisymm
    (hPdec.trans (sup_le (sup_le (hPL₁.trans le_sup_right) (hPL.trans le_sup_left)) le_sup_right))
    (sup_le hRpP inf_le_left)
  have hCpRp : Cp ≤ normalizer (Rp : Set Γ) := inf_le_left.trans hPRp
  have hCpQ₀ : Cp ≤ normalizer (Q₀ : Set Γ) := inf_le_right.trans hH₀Q₀
  have hPNt : P ≤ normalizer (Nt : Set Γ) := le_normalizer_sup_of_le_normalizer hPQ₁ hPRt
  have hCpNt : Cp ≤ normalizer (Nt : Set Γ) := inf_le_left.trans hPNt
  have hRpNt : Rp ≤ normalizer (Nt : Set Γ) := hRpP.trans hPNt
  have swap : ∀ {H K : Subgroup Γ}, H ≤ normalizer (K : Set Γ) → (H : Set Γ) * K = K * H := by
    intro H K h
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right H K h,
      ← Subgroup.coe_mul_of_right_le_normalizer_left K H h, sup_comm]
  have hF'set : (F' : Set Γ) = (Nt : Set Γ) * Q₀ :=
    Subgroup.coe_mul_of_right_le_normalizer_left Nt Q₀ hQ₀Nt
  have hPset : (P : Set Γ) = (Rp : Set Γ) * Cp :=
    (congrArg (fun K : Subgroup Γ => (K : Set Γ)) hPeq).trans
      (Subgroup.coe_mul_of_right_le_normalizer_left Rp Cp hCpRp)
  have hperm : (F' : Set Γ) * P = P * F' := by
    rw [hF'set, hPset]
    calc (Nt : Set Γ) * Q₀ * (Rp * Cp) = Nt * ((Q₀ * Rp) * Cp) := by simp only [mul_assoc]
      _ = Nt * ((Rp * Q₀) * Cp) := by rw [swap hQ₀Rp]
      _ = Nt * (Rp * (Q₀ * Cp)) := by simp only [mul_assoc]
      _ = Nt * (Rp * (Cp * Q₀)) := by rw [← swap hCpQ₀]
      _ = Nt * Rp * (Cp * Q₀) := by simp only [mul_assoc]
      _ = Rp * Nt * (Cp * Q₀) := by rw [← swap hRpNt]
      _ = Rp * (Nt * Cp) * Q₀ := by simp only [mul_assoc]
      _ = Rp * (Cp * Nt) * Q₀ := by rw [← swap hCpNt]
      _ = Rp * Cp * (Nt * Q₀) := by simp only [mul_assoc]
  exact ⟨F', ⟨le_top, hF't, hAF', hmax⟩, hFF', hperm⟩

end CFSG.GH72
