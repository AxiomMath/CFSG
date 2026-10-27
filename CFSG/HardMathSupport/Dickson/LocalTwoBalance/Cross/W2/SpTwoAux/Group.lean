module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeLayer

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.HardMathSupport.Timmesfeld.CrossChar

section Transport

theorem noNormalPPrime_map_iff {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) (L : Subgroup G) {p : ℕ} :
    NoNormalPPrime p (L.map f) ↔ NoNormalPPrime p L := by
  constructor
  · intro h N hNL hNn hcop
    have hmap : N.map f = ⊥ := by
      refine h (N.map f) (Subgroup.map_mono hNL) ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩ _ ⟨x, hx, rfl⟩
        exact ⟨y * x * y⁻¹, hNn y hy x hx, by simp⟩
      · rwa [Subgroup.card_map_of_injective hf]
    exact (Subgroup.map_eq_bot_iff_of_injective N hf).1 hmap
  · intro h M hML hMn hcop
    set N : Subgroup G := M.comap f ⊓ L
    have hNM : N.map f = M := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx.1
      · intro hy
        obtain ⟨x, hxL, rfl⟩ := hML hy
        exact ⟨x, ⟨hy, hxL⟩, rfl⟩
    have hNbot : N = ⊥ := by
      refine h N inf_le_right ?_ ?_
      · intro y hy x hx
        refine ⟨?_, L.mul_mem (L.mul_mem hy hx.2) (L.inv_mem hy)⟩
        have : f y * f x * (f y)⁻¹ ∈ M := hMn (f y) (Subgroup.mem_map_of_mem f hy) (f x) hx.1
        simpa using this
      · rwa [← Subgroup.card_map_of_injective hf, hNM]
    rw [← hNM, hNbot, Subgroup.map_bot]

theorem core_eq_bot_of_noNormalPPrime {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    {L : Subgroup K} (h : NoNormalPPrime p L) : CFSG.Open.GLAPPrimeCoreOf p L = ⊥ :=
  h _ (CFSG.HardMathSupport.Timmesfeld.Balance.gLAPPrimeCoreOf_le_self' L)
    (fun g hg x hx => CFSG.HardMathSupport.Timmesfeld.Balance.gLAPPrimeCoreOf_conj_mem' g hg x hx)
    (CFSG.HardMathSupport.Timmesfeld.Balance.coprime_card_gLAPPrimeCoreOf' hp L)

theorem noNormalPPrime_top_iff {K : Type*} [Group K] (L : Subgroup K) {p : ℕ} :
    NoNormalPPrime p (⊤ : Subgroup ↥L) ↔ NoNormalPPrime p L := by
  rw [← noNormalPPrime_map_iff L.subtype L.subtype_injective, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem noNormalPPrime_top_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') {p : ℕ}
    (h : NoNormalPPrime p (⊤ : Subgroup G')) : NoNormalPPrime p (⊤ : Subgroup G) := by
  rw [← noNormalPPrime_map_iff e.toMonoidHom e.injective, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.2 e.surjective]
  exact h

end Transport

section Product

theorem noNormalPPrime_pi {p : ℕ} {ι : Type*} [DecidableEq ι] {G : ι → Type*}
    [∀ i, Group (G i)] (h : ∀ i, NoNormalPPrime p (⊤ : Subgroup (G i))) :
    NoNormalPPrime p (⊤ : Subgroup (∀ i, G i)) := by
  intro N _ hNn hNc
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  funext b
  set Nb : Subgroup (G b) := N.map (Pi.evalMonoidHom G b)
  have hNb : Nb = ⊥ := by
    refine h b Nb le_top ?_ ?_
    · rintro y - _ ⟨n, hn, rfl⟩
      refine ⟨Pi.mulSingle b y * n * (Pi.mulSingle b y)⁻¹,
        hNn _ (Subgroup.mem_top _) n hn, ?_⟩
      simp
    · exact hNc.coprime_dvd_right (Subgroup.card_map_dvd N _)
  have : g b ∈ Nb := ⟨g, hg, rfl⟩
  rw [hNb, Subgroup.mem_bot] at this
  simpa using this

theorem noNormalPPrime_iSup {p : ℕ} {G : Type*} [Group G] {ι : Type*} [Finite ι]
    {F : ι → Subgroup G}
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ F i → y ∈ F j → Commute x y)
    (hind : iSupIndep F) (hF : ∀ i, NoNormalPPrime p (F i)) :
    NoNormalPPrime p (⨆ i, F i) := by
  classical
  have := Fintype.ofFinite ι
  let θ := Subgroup.noncommPiCoprod hcomm
  have hθ : Function.Injective θ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hpi : NoNormalPPrime p (⊤ : Subgroup (∀ i, F i)) :=
    noNormalPPrime_pi fun i => (noNormalPPrime_top_iff (F i)).2 (hF i)
  rw [← Subgroup.noncommPiCoprod_range (hcomm := hcomm), MonoidHom.range_eq_map]
  exact (noNormalPPrime_map_iff θ hθ ⊤).2 hpi

end Product

section Kernel

theorem noNormalPPrime_top_of_ker {G A : Type*} [Group G] [Group A] {p : ℕ}
    (φ : G →* A) (hA : ∃ n : ℕ, Nat.card φ.range = p ^ n)
    (hk : NoNormalPPrime p φ.ker) : NoNormalPPrime p (⊤ : Subgroup G) := by
  intro N _ hNn hNc
  have hNk : N ⊓ φ.ker = ⊥ := by
    refine hk (N ⊓ φ.ker) inf_le_right ?_ ?_
    · intro y hy x hx
      refine ⟨hNn y (Subgroup.mem_top y) x hx.1, ?_⟩
      have hy' : φ y = 1 := hy
      have hx' : φ x = 1 := hx.2
      show φ (y * x * y⁻¹) = 1
      rw [map_mul, map_mul, map_inv, hy', hx']
      simp
    · exact hNc.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  set ψ : N →* A := φ.comp N.subtype with hψ
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, hx⟩ hxk
    have hx1 : φ x = 1 := hxk
    have : x ∈ N ⊓ φ.ker := ⟨hx, hx1⟩
    rw [hNk] at this
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 this))
  have hcard : Nat.card N = Nat.card ψ.range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hle : ψ.range ≤ φ.range := by
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    exact ⟨x, rfl⟩
  obtain ⟨n, hn⟩ := hA
  have hdvd : Nat.card N ∣ p ^ n := by
    rw [hcard, ← hn]
    exact Subgroup.card_dvd_of_le hle
  have hcop : Nat.Coprime (Nat.card N) (p ^ n) := Nat.Coprime.pow_right n hNc.symm
  have h1 : Nat.card N = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  exact Subgroup.card_eq_one.1 h1

end Kernel

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
