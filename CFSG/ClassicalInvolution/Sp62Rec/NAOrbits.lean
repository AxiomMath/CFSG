module

public import CFSG.ClassicalInvolution.Sp62Rec.NACount
import CFSG.ClassicalInvolution.Sp62Rec.FiveFix
public import CFSG.ClassicalInvolution.Solomon73
public import CFSG.ClassicalInvolution.Solomon73.YamakiModel

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.Open

section Transport

variable {M N : Type} [Group M] [Group N] [Finite M] [Finite N]

private theorem mem_orbIn_iff' {X : Subgroup M} {a b : M} :
    b ∈ orbIn X a ↔ ∃ x ∈ X, x * a * x⁻¹ = b :=
  Iff.rfl

private theorem orbIn_subset_sub {X : Subgroup M} {c : M} (hc : c ∈ X) :
    orbIn X c ⊆ (X : Set M) := by
  intro b hb
  obtain ⟨x, hx, rfl⟩ := (mem_orbIn_iff').mp hb
  exact X.mul_mem (X.mul_mem hx hc) (X.inv_mem hx)

private theorem image_orbIn_preimage {X : Subgroup M} {Y : Subgroup N}
    (ν : ↥X ≃* ↥Y) (ι : ↥Y →* M) (hι : ∀ m : ↥Y, ι m = ((ν.symm m : ↥X) : M)) (c : ↥Y) :
    ι '' (Subtype.val ⁻¹' orbIn Y (c : N)) = orbIn X (ι c) := by
  ext g
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hn' : (n : N) ∈ orbIn Y (c : N) := hn
    obtain ⟨m, hm, hmn⟩ := (mem_orbIn_iff').mp hn'
    have key : (⟨m, hm⟩ : ↥Y) * c * (⟨m, hm⟩ : ↥Y)⁻¹ = n := Subtype.ext hmn
    refine (mem_orbIn_iff').mpr ⟨((ν.symm ⟨m, hm⟩ : ↥X) : M), (ν.symm ⟨m, hm⟩).2, ?_⟩
    rw [← hι ⟨m, hm⟩, ← key, map_mul, map_mul, map_inv]
  · intro hg
    obtain ⟨x, hx, hxg⟩ := (mem_orbIn_iff').mp hg
    have hmx : ι (ν ⟨x, hx⟩) = x := by
      rw [hι, MulEquiv.symm_apply_apply]
    refine ⟨(ν ⟨x, hx⟩ : ↥Y) * c * (ν ⟨x, hx⟩ : ↥Y)⁻¹, ?_, ?_⟩
    · have hmem : (((ν ⟨x, hx⟩ : ↥Y) * c * (ν ⟨x, hx⟩ : ↥Y)⁻¹ : ↥Y) : N) ∈ orbIn Y (c : N) :=
        (mem_orbIn_iff').mpr ⟨((ν ⟨x, hx⟩ : ↥Y) : N), (ν ⟨x, hx⟩ : ↥Y).2, rfl⟩
      exact hmem
    · rw [map_mul, map_mul, map_inv, hmx, hxg]

private theorem ncard_orbIn_eq {X : Subgroup M} {Y : Subgroup N}
    (ν : ↥X ≃* ↥Y) (ι : ↥Y →* M) (hι : ∀ m : ↥Y, ι m = ((ν.symm m : ↥X) : M)) (c : ↥Y) :
    (orbIn X (ι c)).ncard = (orbIn Y (c : N)).ncard := by
  have hinj : Function.Injective ι := by
    intro m n h
    rw [hι, hι] at h
    exact ν.symm.injective (Subtype.ext h)
  rw [← image_orbIn_preimage ν ι hι c, Set.ncard_image_of_injective _ hinj]
  apply Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
  intro s hs
  exact ⟨⟨s, orbIn_subset_sub c.2 hs⟩, rfl⟩

private theorem card_closure_orbIn_eq {X : Subgroup M} {Y : Subgroup N}
    (ν : ↥X ≃* ↥Y) (ι : ↥Y →* M) (hι : ∀ m : ↥Y, ι m = ((ν.symm m : ↥X) : M)) (c : ↥Y) :
    Nat.card ↥(Subgroup.closure (orbIn X (ι c))) =
      Nat.card ↥(Subgroup.closure (orbIn Y (c : N))) := by
  have hinj : Function.Injective ι := by
    intro m n h
    rw [hι, hι] at h
    exact ν.symm.injective (Subtype.ext h)
  have hmapY : (Subgroup.closure (Subtype.val ⁻¹' orbIn Y (c : N) : Set ↥Y)).map Y.subtype =
      Subgroup.closure (orbIn Y (c : N)) := by
    rw [MonoidHom.map_closure]
    congr 1
    ext s
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact hn
    · intro hs
      exact ⟨⟨s, orbIn_subset_sub c.2 hs⟩, hs, rfl⟩
  have h1 : Nat.card ↥(Subgroup.closure (orbIn Y (c : N))) =
      Nat.card ↥(Subgroup.closure (Subtype.val ⁻¹' orbIn Y (c : N) : Set ↥Y)) := by
    rw [← hmapY, Subgroup.card_map_of_injective (Subgroup.subtype_injective Y)]
  rw [h1, ← image_orbIn_preimage ν ι hι c, ← MonoidHom.map_closure,
    Subgroup.card_map_of_injective (f := ι) hinj]

end Transport

variable {G : Type} [Group G] [Finite G] {A X' : Subgroup G}
  {e y : G} {A0 : Subgroup (StatedSp 3 (ZMod 2))} {rho : StatedSp 3 (ZMod 2)}

theorem mem_normalizer_iff_theta (θ : ↥(Subgroup.centralizer ({e} : Set G)) ≃* ↥Hhat)
    (hACe : A ≤ Subgroup.centralizer ({e} : Set G))
    (hθA : (A.subgroupOf (Subgroup.centralizer ({e} : Set G))).map θ.toMonoidHom =
      A0.subgroupOf Hhat)
    (hA0H : A0 ≤ Hhat)
    (hNX0 : ∀ x ∈ Hhat, x ∈ Subgroup.normalizer (A0 : Set (StatedSp 3 (ZMod 2))) → x ∈ X0)
    (hX0N : X0 ≤ Subgroup.normalizer (A0 : Set (StatedSp 3 (ZMod 2))))
    (x : G) (hx : x ∈ Subgroup.centralizer ({e} : Set G)) :
    x ∈ Subgroup.normalizer (A : Set G) ↔ ((θ ⟨x, hx⟩ : ↥Hhat) : StatedSp 3 (ZMod 2)) ∈ X0 := by
  obtain ⟨t, ht⟩ : ∃ t : ↥Hhat, θ ⟨x, hx⟩ = t := ⟨_, rfl⟩
  rw [ht]
  have F1 : ∀ p : ↥(Subgroup.centralizer ({e} : Set G)),
      (p : G) ∈ A ↔ ((θ p : ↥Hhat) : StatedSp 3 (ZMod 2)) ∈ A0 := by
    intro p
    have h1 : θ p ∈ (A.subgroupOf (Subgroup.centralizer ({e} : Set G))).map θ.toMonoidHom ↔
        p ∈ A.subgroupOf (Subgroup.centralizer ({e} : Set G)) := by
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    rw [hθA, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h1
    exact h1.symm
  have Fconj : ∀ p : ↥(Subgroup.centralizer ({e} : Set G)),
      ((θ ((⟨x, hx⟩ : ↥(Subgroup.centralizer ({e} : Set G))) * p *
        (⟨x, hx⟩ : ↥(Subgroup.centralizer ({e} : Set G)))⁻¹) : ↥Hhat) : StatedSp 3 (ZMod 2)) =
        (t : StatedSp 3 (ZMod 2)) * ((θ p : ↥Hhat) : StatedSp 3 (ZMod 2)) *
          (t : StatedSp 3 (ZMod 2))⁻¹ := by
    intro p
    simp only [map_mul, map_inv, ht, Subgroup.coe_mul, Subgroup.coe_inv]
  have hxN : x ∈ Subgroup.normalizer (A : Set G) ↔
      (t : StatedSp 3 (ZMod 2)) ∈ Subgroup.normalizer (A0 : Set (StatedSp 3 (ZMod 2))) := by
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro hxA b
      have hxA' : ∀ n : G, n ∈ A ↔ x * n * x⁻¹ ∈ A := fun n => hxA n
      constructor
      · intro hb
        have hbH : b ∈ Hhat := hA0H hb
        obtain ⟨p, hp⟩ : ∃ p : ↥(Subgroup.centralizer ({e} : Set G)), θ p = ⟨b, hbH⟩ :=
          ⟨θ.symm ⟨b, hbH⟩, θ.apply_symm_apply _⟩
        have hθp : ((θ p : ↥Hhat) : StatedSp 3 (ZMod 2)) = b := congrArg Subtype.val hp
        have hpA : (p : G) ∈ A := (F1 p).mpr (by rw [hθp]; exact hb)
        have h2 := (F1 (⟨x, hx⟩ * p * (⟨x, hx⟩ : ↥(Subgroup.centralizer ({e} : Set G)))⁻¹)).mp
          ((hxA' p).mp hpA)
        rw [Fconj p, hθp] at h2
        exact h2
      · intro htb
        have htbH : (t : StatedSp 3 (ZMod 2)) * b * (t : StatedSp 3 (ZMod 2))⁻¹ ∈ Hhat :=
          hA0H htb
        have hbH : b ∈ Hhat := by
          have h := Hhat.mul_mem (Hhat.mul_mem (Hhat.inv_mem t.2) htbH) t.2
          have e' : (t : StatedSp 3 (ZMod 2))⁻¹ * ((t : StatedSp 3 (ZMod 2)) * b *
              (t : StatedSp 3 (ZMod 2))⁻¹) * (t : StatedSp 3 (ZMod 2)) = b := by
            group
          rwa [e'] at h
        obtain ⟨p, hp⟩ : ∃ p : ↥(Subgroup.centralizer ({e} : Set G)), θ p = ⟨b, hbH⟩ :=
          ⟨θ.symm ⟨b, hbH⟩, θ.apply_symm_apply _⟩
        have hθp : ((θ p : ↥Hhat) : StatedSp 3 (ZMod 2)) = b := congrArg Subtype.val hp
        have h1 : ((θ (⟨x, hx⟩ * p * (⟨x, hx⟩ : ↥(Subgroup.centralizer ({e} : Set G)))⁻¹) :
            ↥Hhat) : StatedSp 3 (ZMod 2)) ∈ A0 := by
          rw [Fconj p, hθp]
          exact htb
        have hxpA := (F1 (⟨x, hx⟩ * p * (⟨x, hx⟩ : ↥(Subgroup.centralizer ({e} : Set G)))⁻¹)).mpr h1
        have hpA : (p : G) ∈ A := (hxA' p).mpr hxpA
        have h2 := (F1 p).mp hpA
        rw [hθp] at h2
        exact h2
    · intro htN n
      by_cases hn : n ∈ Subgroup.centralizer ({e} : Set G)
      · have hb := htN ((θ ⟨n, hn⟩ : ↥Hhat) : StatedSp 3 (ZMod 2))
        have h1 := F1 ⟨n, hn⟩
        have h2 := F1 (⟨x, hx⟩ * ⟨n, hn⟩ * (⟨x, hx⟩ : ↥(Subgroup.centralizer ({e} : Set G)))⁻¹)
        rw [Fconj ⟨n, hn⟩] at h2
        exact h1.trans (hb.trans h2.symm)
      · have hnA : n ∉ A := fun h => hn (hACe h)
        have hxnx : x * n * x⁻¹ ∉ A := fun h => hn (by
          have hC : x * n * x⁻¹ ∈ Subgroup.centralizer ({e} : Set G) := hACe h
          have hn' : n = x⁻¹ * (x * n * x⁻¹) * x := by group
          rw [hn']
          exact mul_mem (mul_mem (inv_mem hx) hC) hx)
        exact ⟨fun h => (hnA h).elim, fun h => (hxnx h).elim⟩
  refine hxN.trans ⟨fun h => hNX0 _ t.2 h, fun h => hX0N h⟩

theorem card_normalizer_inf_centralizer (θ : ↥(Subgroup.centralizer ({e} : Set G)) ≃* ↥Hhat)
    (hACe : A ≤ Subgroup.centralizer ({e} : Set G))
    (hθA : (A.subgroupOf (Subgroup.centralizer ({e} : Set G))).map θ.toMonoidHom =
      A0.subgroupOf Hhat)
    (hA0H : A0 ≤ Hhat)
    (hNX0 : ∀ x ∈ Hhat, x ∈ Subgroup.normalizer (A0 : Set (StatedSp 3 (ZMod 2))) → x ∈ X0)
    (hX0N : X0 ≤ Subgroup.normalizer (A0 : Set (StatedSp 3 (ZMod 2)))) :
    Nat.card ↥(Subgroup.normalizer (A : Set G) ⊓ Subgroup.centralizer ({e} : Set G)) =
      Nat.card X0 := by
  have himg : ((Subgroup.normalizer (A : Set G) ⊓ Subgroup.centralizer ({e} : Set G)).subgroupOf
      (Subgroup.centralizer ({e} : Set G))).map θ.toMonoidHom = X0.subgroupOf Hhat := by
    ext h
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hp
      rw [Subgroup.mem_subgroupOf]
      exact (mem_normalizer_iff_theta θ hACe hθA hA0H hNX0 hX0N (p : G) p.2).mp hp.1
    · intro hh
      rw [Subgroup.mem_subgroupOf] at hh
      refine ⟨θ.symm h, ?_, θ.apply_symm_apply h⟩
      have hmem := (mem_normalizer_iff_theta θ hACe hθA hA0H hNX0 hX0N _
        (θ.symm h).2).mpr (by
          have hq : θ ⟨((θ.symm h : ↥(Subgroup.centralizer ({e} : Set G))) : G),
              (θ.symm h).2⟩ = h := θ.apply_symm_apply h
          rw [hq]
          exact hh)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨hmem, (θ.symm h).2⟩
  have hcardN : Nat.card ↥((Subgroup.normalizer (A : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)).subgroupOf (Subgroup.centralizer ({e} : Set G))) =
      Nat.card ↥(Subgroup.normalizer (A : Set G) ⊓ Subgroup.centralizer ({e} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hcardX : Nat.card ↥(X0.subgroupOf Hhat) = Nat.card X0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe X0_le_Hhat).toEquiv
  rw [← hcardN, ← hcardX, ← himg,
    Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective]

theorem normalizer_eq_of_nu (θ : ↥(Subgroup.centralizer ({e} : Set G)) ≃* ↥Hhat)
    (hACe : A ≤ Subgroup.centralizer ({e} : Set G))
    (hθA : (A.subgroupOf (Subgroup.centralizer ({e} : Set G))).map θ.toMonoidHom =
      A0.subgroupOf Hhat)
    (hA : IsE64 A) (heA : e ∈ A) (hCA : Subgroup.centralizer (A : Set G) = A)
    (hXN : X' ≤ Subgroup.normalizer (A : Set G)) (hAX : A ≤ X')
    (ν : ↥X' ≃* ↥N0) (hνA : (A.subgroupOf X').map ν.toMonoidHom = A0.subgroupOf N0)
    (hνe : ((ν ⟨e, hAX heA⟩ : ↥N0) : StatedSp 3 (ZMod 2)) = alpha)
    (hyA : y ∈ A) (hνy : ((ν ⟨y, hAX hyA⟩ : ↥N0) : StatedSp 3 (ZMod 2)) = pi12)
    (hrig : ∀ g : G, g * e * g⁻¹ ≠ y ∧ g * e * g⁻¹ ≠ e * y ∧ g * y * g⁻¹ ≠ e * y)
    (hcover : ∀ a ∈ A0, a ≠ 1 → a ∈ orbIn N0 alpha ∨ a ∈ orbIn N0 pi12 ∨ a ∈ orbIn N0 pi3 ∨
      a ∈ orbIn N0 rho)
    (hrhoA0 : rho ∈ A0)
    (horbα : (orbIn N0 alpha).ncard = 7) (horbρ : (orbIn N0 rho).ncard = 28)
    (hD : Nat.card (Subgroup.closure (orbIn N0 pi12)) = 8)
    (hX0 : Nat.card X0 = 1536) (hN0 : Nat.card N0 = 10752)
    (hNX0 : ∀ x ∈ Hhat, x ∈ Subgroup.normalizer (A0 : Set (StatedSp 3 (ZMod 2))) → x ∈ X0)
    (hX0N : X0 ≤ Subgroup.normalizer (A0 : Set (StatedSp 3 (ZMod 2)))) :
    Subgroup.normalizer (A : Set G) = X' := by
  have hνmem : ∀ x : ↥X', (x : G) ∈ A → ((ν x : ↥N0) : StatedSp 3 (ZMod 2)) ∈ A0 := by
    intro x hx
    have h1 : ν x ∈ (A.subgroupOf X').map ν.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hνA, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hmemν : ∀ x : ↥X', ((ν x : ↥N0) : StatedSp 3 (ZMod 2)) ∈ A0 → (x : G) ∈ A := by
    intro x hx
    have h1 : ν x ∈ (A.subgroupOf X').map ν.toMonoidHom := by
      rw [hνA, Subgroup.mem_subgroupOf]
      exact hx
    obtain ⟨x', hx', hxx⟩ := Subgroup.mem_map.mp h1
    have hxx' : x' = x := ν.injective hxx
    rw [← hxx']
    exact Subgroup.mem_subgroupOf.mp hx'
  have hαN0 : alpha ∈ N0 := by
    have h := (ν ⟨e, hAX heA⟩).2
    rwa [hνe] at h
  have hπN0 : pi12 ∈ N0 := by
    have h := (ν ⟨y, hAX hyA⟩).2
    rwa [hνy] at h
  have hpi3N0 : pi3 ∈ N0 := N0.mul_mem hαN0 hπN0
  have hcardB0 : Nat.card ↥(A0.subgroupOf N0) = 64 := by
    rw [← hνA, Subgroup.card_map_of_injective (f := ν.toMonoidHom) ν.injective]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv).trans hA.2.2
  have hA0N0 : A0 ≤ N0 := by
    intro a ha
    by_contra haN
    have hsub : ∀ n : ↥(A0.subgroupOf N0), a * (n : StatedSp 3 (ZMod 2)) ∈ orbIn N0 rho := by
      intro n
      have hnN0 : (n : StatedSp 3 (ZMod 2)) ∈ N0 := (n : ↥N0).2
      have hnA0 : (n : StatedSp 3 (ZMod 2)) ∈ A0 := Subgroup.mem_subgroupOf.mp n.2
      have hanA0 : a * (n : StatedSp 3 (ZMod 2)) ∈ A0 := A0.mul_mem ha hnA0
      have hanN : a * (n : StatedSp 3 (ZMod 2)) ∉ N0 := fun h => haN (by
        have h' := N0.mul_mem h (N0.inv_mem hnN0)
        simpa using h')
      have hne : a * (n : StatedSp 3 (ZMod 2)) ≠ 1 := fun h => hanN (by
        rw [h]
        exact N0.one_mem)
      rcases hcover _ hanA0 hne with h | h | h | h
      · exact (hanN (orbIn_subset_sub hαN0 h)).elim
      · exact (hanN (orbIn_subset_sub hπN0 h)).elim
      · exact (hanN (orbIn_subset_sub hpi3N0 h)).elim
      · exact h
    have hinj : Function.Injective (fun n : ↥(A0.subgroupOf N0) =>
        (⟨a * (n : StatedSp 3 (ZMod 2)), hsub n⟩ : ↥(orbIn N0 rho))) := by
      intro n m hnm
      have h1 : a * (n : StatedSp 3 (ZMod 2)) = a * (m : StatedSp 3 (ZMod 2)) :=
        congrArg Subtype.val hnm
      have h2 : (n : StatedSp 3 (ZMod 2)) = (m : StatedSp 3 (ZMod 2)) := mul_left_cancel h1
      exact Subtype.ext (Subtype.ext h2)
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [hcardB0, Nat.card_coe_set_eq, horbρ] at hle
    omega
  have hrhoN0 : rho ∈ N0 := hA0N0 hrhoA0
  have hA0card : Nat.card ↥A0 = 64 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA0N0).toEquiv).symm.trans hcardB0
  have hcardBH : Nat.card ↥(A0.subgroupOf Hhat) = 64 := by
    rw [← hθA, Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hACe).toEquiv).trans hA.2.2
  have hA0H : A0 ≤ Hhat := by
    have h1 : Nat.card ↥(A0 ⊓ Hhat) = 64 := by
      rw [← Subgroup.subgroupOf_map_subtype A0 Hhat,
        Subgroup.card_map_of_injective (f := Hhat.subtype) (Subgroup.subtype_injective Hhat)]
      exact hcardBH
    have h2 : A0 ⊓ Hhat = A0 := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    intro a ha
    have h3 : a ∈ A0 ⊓ Hhat := by
      rw [h2]
      exact ha
    exact (Subgroup.mem_inf.mp h3).2
  obtain ⟨ι, hι⟩ : ∃ ι : ↥N0 →* G, ∀ m : ↥N0, ι m = ((ν.symm m : ↥X') : G) :=
    ⟨X'.subtype.comp ν.symm.toMonoidHom, fun m => rfl⟩
  have hιν : ∀ x : ↥X', ι (ν x) = (x : G) := fun x => by
    rw [hι, MulEquiv.symm_apply_apply]
  have hιe : ι ⟨alpha, hαN0⟩ = e := by
    have h := hιν ⟨e, hAX heA⟩
    rw [show ν ⟨e, hAX heA⟩ = ⟨alpha, hαN0⟩ from Subtype.ext hνe] at h
    exact h
  have hιy : ι ⟨pi12, hπN0⟩ = y := by
    have h := hιν ⟨y, hAX hyA⟩
    rw [show ν ⟨y, hAX hyA⟩ = ⟨pi12, hπN0⟩ from Subtype.ext hνy] at h
    exact h
  have hιpi3 : ι ⟨pi3, hpi3N0⟩ = e * y := by
    have h : (⟨pi3, hpi3N0⟩ : ↥N0) = ⟨alpha, hαN0⟩ * ⟨pi12, hπN0⟩ := Subtype.ext rfl
    rw [h, map_mul, hιe, hιy]
  have hmemorb : ∀ c b : ↥N0, (b : StatedSp 3 (ZMod 2)) ∈ orbIn N0 (c : StatedSp 3 (ZMod 2)) →
      ι b ∈ orbIn X' (ι c) := by
    intro c b hb
    rw [← image_orbIn_preimage ν ι hι c]
    exact ⟨b, hb, rfl⟩
  have hr : ι ⟨rho, hrhoN0⟩ ∈ A := by
    have h1 : ((ν (ν.symm ⟨rho, hrhoN0⟩) : ↥N0) : StatedSp 3 (ZMod 2)) ∈ A0 := by
      rw [MulEquiv.apply_symm_apply]
      exact hrhoA0
    rw [hι]
    exact hmemν (ν.symm ⟨rho, hrhoN0⟩) h1
  have hcover' : ∀ a ∈ A, a ≠ 1 → a ∈ orbIn X' e ∨ a ∈ orbIn X' y ∨ a ∈ orbIn X' (e * y) ∨
      a ∈ orbIn X' (ι ⟨rho, hrhoN0⟩) := by
    intro a ha ha1
    have hbA0 : ((ν ⟨a, hAX ha⟩ : ↥N0) : StatedSp 3 (ZMod 2)) ∈ A0 := hνmem ⟨a, hAX ha⟩ ha
    have hb1 : ((ν ⟨a, hAX ha⟩ : ↥N0) : StatedSp 3 (ZMod 2)) ≠ 1 := by
      intro h
      apply ha1
      have hx1 : ν ⟨a, hAX ha⟩ = 1 := Subtype.ext h
      have hx2 : (⟨a, hAX ha⟩ : ↥X') = 1 := ν.injective (hx1.trans (map_one ν).symm)
      exact congrArg Subtype.val hx2
    have hιa : ι (ν ⟨a, hAX ha⟩) = a := hιν ⟨a, hAX ha⟩
    rcases hcover _ hbA0 hb1 with h | h | h | h
    · left
      have h1 := hmemorb ⟨alpha, hαN0⟩ (ν ⟨a, hAX ha⟩) h
      rwa [hιa, hιe] at h1
    · right
      left
      have h1 := hmemorb ⟨pi12, hπN0⟩ (ν ⟨a, hAX ha⟩) h
      rwa [hιa, hιy] at h1
    · right
      right
      left
      have h1 := hmemorb ⟨pi3, hpi3N0⟩ (ν ⟨a, hAX ha⟩) h
      rwa [hιa, hιpi3] at h1
    · right
      right
      right
      have h1 := hmemorb ⟨rho, hrhoN0⟩ (ν ⟨a, hAX ha⟩) h
      rwa [hιa] at h1
  have hX'card : Nat.card ↥X' = 10752 := (Nat.card_congr ν.toEquiv).trans hN0
  have hcard : Nat.card ↥X' =
      7 * Nat.card ↥(Subgroup.normalizer (A : Set G) ⊓ Subgroup.centralizer ({e} : Set G)) := by
    have h1 := card_normalizer_inf_centralizer θ hACe hθA hA0H hNX0 hX0N
    omega
  have hfive : ∀ (D : Subgroup G) (g : G), D ≤ A → Nat.card D = 8 →
      (∀ a ∈ A, g * a * g⁻¹ ∈ A) → (∀ d ∈ D, g * d * g⁻¹ ∈ D) → g ^ 5 = 1 →
      ∀ a ∈ A, g * a = a * g :=
    fun D g hDA hD8 hgA hgD hg5 => forall_commute_of_pow_five hA.2.2 hDA hD8 hgA hgD hg5
  have hCA' : ∀ g : G, (∀ a ∈ A, g * a = a * g) → g ∈ A := by
    intro g hg
    have hgC : g ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (hg h hh).symm
    rw [hCA] at hgC
    exact hgC
  have horbe' : (orbIn X' e).ncard = 7 := by
    have h := ncard_orbIn_eq ν ι hι ⟨alpha, hαN0⟩
    rw [hιe] at h
    exact h.trans horbα
  have horbr' : (orbIn X' (ι ⟨rho, hrhoN0⟩)).ncard = 28 :=
    (ncard_orbIn_eq ν ι hι ⟨rho, hrhoN0⟩).trans horbρ
  have hD' : Nat.card ↥(Subgroup.closure (orbIn X' y)) = 8 := by
    have h := card_closure_orbIn_eq ν ι hι ⟨pi12, hπN0⟩
    rw [hιy] at h
    exact h.trans hD
  exact normalizer_eq_of_orbits hA.2.1 hA.2.2 hCA' hXN heA hyA hr hcover' horbe' horbr' hD' hrig
    hcard hfive

end CFSG.ClassicalInvolution.Sp62Rec
